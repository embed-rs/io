// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use prelude::*;

use core::cmp;
use core::fmt;
use impls::{FailedToFillWholeBuffer, FailedToWriteWholeBuffer};
use ::{SeekFrom, Error};

/// A `Cursor` wraps another type and provides it with a
/// [`Seek`] implementation.
///
/// `Cursor`s are typically used with in-memory buffers to allow them to
/// implement [`Read`] and/or [`Write`], allowing these buffers to be used
/// anywhere you might use a reader or writer that does actual I/O.
///
/// The standard library implements some I/O traits on various types which
/// are commonly used as a buffer, like `Cursor<`[`Vec`]`<u8>>` and
/// `Cursor<`[`&[u8]`][bytes]`>`.
///
/// # Examples
///
/// We may want to write bytes to a [`File`] in our production
/// code, but use an in-memory buffer in our tests. We can do this with
/// `Cursor`:
///
/// [`Seek`]: trait.Seek.html
/// [`Read`]: ../../std/io/trait.Read.html
/// [`Write`]: ../../std/io/trait.Write.html
/// [`Vec`]: ../../std/vec/struct.Vec.html
/// [bytes]: ../../std/primitive.slice.html
/// [`File`]: ../fs/struct.File.html
///
/// ```no_run
/// use std::io::prelude::*;
/// use std::io::{self, SeekFrom};
/// use std::fs::File;
///
/// // a library function we've written
/// fn write_ten_bytes_at_end<W: Write + Seek>(writer: &mut W) -> io::Result<()> {
///     try!(writer.seek(SeekFrom::End(-10)));
///
///     for i in 0..10 {
///         try!(writer.write(&[i]));
///     }
///
///     // all went well
///     Ok(())
/// }
///
/// # fn foo() -> io::Result<()> {
/// // Here's some code that uses this library function.
/// //
/// // We might want to use a BufReader here for efficiency, but let's
/// // keep this example focused.
/// let mut file = try!(File::create("foo.txt"));
///
/// try!(write_ten_bytes_at_end(&mut file));
/// # Ok(())
/// # }
///
/// // now let's write a test
/// #[test]
/// fn test_writes_bytes() {
///     // setting up a real File is much more slow than an in-memory buffer,
///     // let's use a cursor instead
///     use std::io::Cursor;
///     let mut buff = Cursor::new(vec![0; 15]);
///
///     write_ten_bytes_at_end(&mut buff).unwrap();
///
///     assert_eq!(&buff.get_ref()[5..15], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

impl<T> Cursor<T> {
    /// Creates a new cursor wrapping the provided underlying I/O object.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    ///
    /// let buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    /// ```
    pub fn new(inner: T) -> Cursor<T> {
        Cursor { pos: 0, inner: inner }
    }

    /// Consumes this cursor, returning the underlying value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    ///
    /// let buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    ///
    /// let vec = buff.into_inner();
    /// ```
    pub fn into_inner(self) -> T { self.inner }

    /// Gets a reference to the underlying value in this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    ///
    /// let buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    ///
    /// let reference = buff.get_ref();
    /// ```
    pub fn get_ref(&self) -> &T { &self.inner }

    /// Gets a mutable reference to the underlying value in this cursor.
    ///
    /// Care should be taken to avoid modifying the internal I/O state of the
    /// underlying value as it may corrupt this cursor's position.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    ///
    /// let mut buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    ///
    /// let reference = buff.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut T { &mut self.inner }

    /// Returns the current position of this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    /// use std::io::prelude::*;
    /// use std::io::SeekFrom;
    ///
    /// let mut buff = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buff.position(), 0);
    ///
    /// buff.seek(SeekFrom::Current(2)).unwrap();
    /// assert_eq!(buff.position(), 2);
    ///
    /// buff.seek(SeekFrom::Current(-1)).unwrap();
    /// assert_eq!(buff.position(), 1);
    /// ```
    pub fn position(&self) -> u64 { self.pos }

    /// Sets the position of this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    ///
    /// let mut buff = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buff.position(), 0);
    ///
    /// buff.set_position(2);
    /// assert_eq!(buff.position(), 2);
    ///
    /// buff.set_position(4);
    /// assert_eq!(buff.position(), 4);
    /// ```
    pub fn set_position(&mut self, pos: u64) { self.pos = pos; }
}

pub struct InvalidSeekToNegativePosition;

impl Error for InvalidSeekToNegativePosition {
    fn unexpected_eof(_: &'static str) -> Self {
        panic!("don't use InvalidSeekToNegativePosition");
    }
    fn is_interrupted(&self) -> bool { false }
    fn write_zero(_: &'static str) -> Self { panic!("don't use InvalidSeekToNegativePosition") }
    fn other(_: &'static str) -> Self { panic!("don't use InvalidSeekToNegativePosition") }
}

impl fmt::Debug for InvalidSeekToNegativePosition {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str("invalid seek to a negative position")
    }
}

impl<T> Seek for Cursor<T> where T: AsRef<[u8]> {
    type Error = InvalidSeekToNegativePosition;
    fn seek(&mut self, style: SeekFrom) -> Result<u64, InvalidSeekToNegativePosition> {
        let pos = match style {
            SeekFrom::Start(n) => { self.pos = n; return Ok(n) }
            SeekFrom::End(n) => self.inner.as_ref().len() as i64 + n,
            SeekFrom::Current(n) => self.pos as i64 + n,
        };

        if pos < 0 {
            Err(InvalidSeekToNegativePosition)
        } else {
            self.pos = pos as u64;
            Ok(self.pos)
        }
    }
}

impl<T> Read for Cursor<T> where T: AsRef<[u8]> {
    type Error = FailedToFillWholeBuffer;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, FailedToFillWholeBuffer> {
        let n = Read::read(&mut self.fill_buf()?, buf)?;
        self.pos += n as u64;
        Ok(n)
    }
}

impl<T> BufRead for Cursor<T> where T: AsRef<[u8]> {
    fn fill_buf(&mut self) -> Result<&[u8], FailedToFillWholeBuffer> {
        let amt = cmp::min(self.pos, self.inner.as_ref().len() as u64);
        Ok(&self.inner.as_ref()[(amt as usize)..])
    }
    fn consume(&mut self, amt: usize) { self.pos += amt as u64; }
}

impl<'a> Write for Cursor<&'a mut [u8]> {
    type Error = FailedToWriteWholeBuffer;
    #[inline]
    fn write(&mut self, data: &[u8]) -> Result<usize, FailedToWriteWholeBuffer> {
        let pos = cmp::min(self.pos, self.inner.len() as u64);
        let amt = (&mut self.inner[(pos as usize)..]).write(data)?;
        self.pos += amt as u64;
        Ok(amt)
    }
    fn flush(&mut self) -> Result<(), FailedToWriteWholeBuffer> { Ok(()) }
}
