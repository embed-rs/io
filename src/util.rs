// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(missing_copy_implementations)]

use ::{Read, Write, Error, BufRead, Void};

/// Copies the entire contents of a reader into a writer.
///
/// This function will continuously read data from `reader` and then
/// write it into `writer` in a streaming fashion until `reader`
/// returns EOF.
///
/// On success, the total number of bytes that were copied from
/// `reader` to `writer` is returned.
///
/// # Errors
///
/// This function will return an error immediately if any call to `read` or
/// `write` returns an error. All instances of `ErrorKind::Interrupted` are
/// handled by this function and the underlying operation is retried.
///
/// # Examples
///
/// ```
/// use std::io;
///
/// # fn foo() -> io::Result<()> {
/// let mut reader: &[u8] = b"hello";
/// let mut writer: Vec<u8> = vec![];
///
/// try!(io::copy(&mut reader, &mut writer));
///
/// assert_eq!(reader, &writer[..]);
/// # Ok(())
/// # }
/// ```
pub fn copy<E: Error, R: ?Sized, W: ?Sized>(reader: &mut R, writer: &mut W) -> Result<u64, E>
    where R: Read<Error = E>, W: Write<Error = E>
{
    let mut buf = [0; super::DEFAULT_BUF_SIZE];
    let mut written = 0;
    loop {
        let len = match reader.read(&mut buf) {
            Ok(0) => return Ok(written),
            Ok(len) => len,
            Err(ref e) if e.is_interrupted() => continue,
            Err(e) => return Err(e),
        };
        writer.write_all(&buf[..len])?;
        written += len as u64;
    }
}

/// A reader which is always at EOF.
///
/// This struct is generally created by calling [`empty()`][empty]. Please see
/// the documentation of `empty()` for more details.
///
/// [empty]: fn.empty.html
#[derive(Debug)]
pub struct Empty { _priv: () }

/// Constructs a new handle to an empty reader.
///
/// All reads from the returned reader will return `Ok(0)`.
///
/// # Examples
///
/// A slightly sad example of not reading anything into a buffer:
///
/// ```
/// use std::io::{self, Read};
///
/// let mut buffer = String::new();
/// io::empty().read_to_string(&mut buffer).unwrap();
/// assert!(buffer.is_empty());
/// ```
pub fn empty() -> Empty { Empty { _priv: () } }

impl Read for Empty {
    type Error = Void;
    fn read(&mut self, _buf: &mut [u8]) -> Result<usize, Void> { Ok(0) }
}
impl BufRead for Empty {
    fn fill_buf(&mut self) -> Result<&[u8], Void> { Ok(&[]) }
    fn consume(&mut self, _n: usize) {}
}

/// A reader which yields one byte over and over and over and over and over and...
///
/// This struct is generally created by calling [`repeat()`][repeat]. Please
/// see the documentation of `repeat()` for more details.
///
/// [repeat]: fn.repeat.html
#[derive(Debug)]
pub struct Repeat { byte: u8 }

/// Creates an instance of a reader that infinitely repeats one byte.
///
/// All reads from this reader will succeed by filling the specified buffer with
/// the given byte.
///
/// # Examples
///
/// ```
/// use std::io::{self, Read};
///
/// let mut buffer = [0; 3];
/// io::repeat(0b101).read_exact(&mut buffer).unwrap();
/// assert_eq!(buffer, [0b101, 0b101, 0b101]);
/// ```
pub fn repeat(byte: u8) -> Repeat { Repeat { byte: byte } }

impl Read for Repeat {
    type Error = Void;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Void> {
        for slot in &mut *buf {
            *slot = self.byte;
        }
        Ok(buf.len())
    }
}

/// A writer which will move data into the void.
///
/// This struct is generally created by calling [`sink()`][sink]. Please
/// see the documentation of `sink()` for more details.
///
/// [sink]: fn.sink.html
#[derive(Debug)]
pub struct Sink { _priv: () }

/// Creates an instance of a writer which will successfully consume all data.
///
/// All calls to `write` on the returned instance will return `Ok(buf.len())`
/// and the contents of the buffer will not be inspected.
///
/// # Examples
///
/// ```rust
/// use std::io::{self, Write};
///
/// let buffer = vec![1, 2, 3, 5, 8];
/// let num_bytes = io::sink().write(&buffer).unwrap();
/// assert_eq!(num_bytes, 5);
/// ```
pub fn sink() -> Sink { Sink { _priv: () } }

impl Write for Sink {
    type Error = Void;
    fn write(&mut self, buf: &[u8]) -> Result<usize, Void> { Ok(buf.len()) }
    fn flush(&mut self) -> Result<(), Void> { Ok(()) }
}

#[cfg(test)]
mod tests {
    
}
