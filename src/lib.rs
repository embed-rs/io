#![cfg_attr(feature = "unstable", feature(never_type))]
#![cfg_attr(not(feature = "std"), no_std)]

//! This crate allows the implementation of readers and writers without requiring the
//! standard library or even an explicit `Error` type. Convenience implementations exist
//! such that if an algorithm works on the generic impl, it also will work for
//! the standard libraries file and stdio types.

#[cfg(feature = "std")]
extern crate core;

use core::cmp;
use core::fmt;
use core::result;

pub use self::buffered::{BufReader, BufWriter, LineWriter};
pub use self::buffered::IntoInnerError;
pub use self::cursor::Cursor;
pub use self::util::{copy, sink, Sink, empty, Empty, repeat, Repeat};
pub use self::error::Error;

const DEFAULT_BUF_SIZE: usize = 8 * 1024;

pub mod prelude;
mod buffered;
mod cursor;
mod impls;
mod util;
mod error;
mod str;
// FIXME: upstream to libcore
mod memchr;

#[cfg(feature = "std")]
mod std_impls;

#[cfg(feature = "unstable")]
type Void = !;

#[cfg(not(feature = "unstable"))]
pub enum Void {}

/// The `Read` trait allows for reading bytes from a source.
///
/// Implementors of the `Read` trait are sometimes called 'readers'.
///
/// Readers are defined by one required method, `read()`. Each call to `read`
/// will attempt to pull bytes from this source into a provided buffer. A
/// number of other methods are implemented in terms of `read()`, giving
/// implementors a number of ways to read bytes while only needing to implement
/// a single method.
///
/// Readers are intended to be composable with one another. Many implementors
/// throughout `std::io` take and provide types which implement the `Read`
/// trait.
///
/// Please note that each call to `read` may involve a system call, and
/// therefore, using something that implements [`BufRead`][bufread], such as
/// [`BufReader`][bufreader], will be more efficient.
///
/// [bufread]: trait.BufRead.html
/// [bufreader]: struct.BufReader.html
///
pub trait Read {
    /// All `Read` impls will need to supply an error type.
    /// The `std` types will automatically supply `std::io::Error`
    type Error: Error;
    /// Pull some bytes from this source into the specified buffer, returning
    /// how many bytes were read.
    ///
    /// This function does not provide any guarantees about whether it blocks
    /// waiting for data, but if an object needs to block for a read but cannot
    /// it will typically signal this via an `Err` return value.
    ///
    /// If the return value of this method is `Ok(n)`, then it must be
    /// guaranteed that `0 <= n <= buf.len()`. A nonzero `n` value indicates
    /// that the buffer `buf` has been filled in with `n` bytes of data from this
    /// source. If `n` is `0`, then it can indicate one of two scenarios:
    ///
    /// 1. This reader has reached its "end of file" and will likely no longer
    ///    be able to produce bytes. Note that this does not mean that the
    ///    reader will *always* no longer be able to produce bytes.
    /// 2. The buffer specified was 0 bytes in length.
    ///
    /// No guarantees are provided about the contents of `buf` when this
    /// function is called, implementations cannot rely on any property of the
    /// contents of `buf` being true. It is recommended that implementations
    /// only write data to `buf` instead of reading its contents.
    ///
    /// # Errors
    ///
    /// If this function encounters any form of I/O or other error, an error
    /// variant will be returned. If an error is returned then it must be
    /// guaranteed that no bytes were read.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error>;

    /// Read the exact number of bytes required to fill `buf`.
    ///
    /// This function reads as many bytes as necessary to completely fill the
    /// specified buffer `buf`.
    ///
    /// No guarantees are provided about the contents of `buf` when this
    /// function is called, implementations cannot rely on any property of the
    /// contents of `buf` being true. It is recommended that implementations
    /// only write data to `buf` instead of reading its contents.
    ///
    /// # Errors
    ///
    /// If this function encounters an error of the kind
    /// `ErrorKind::Interrupted` then the error is ignored and the operation
    /// will continue.
    ///
    /// If this function encounters an "end of file" before completely filling
    /// the buffer, it returns an error of the kind `ErrorKind::UnexpectedEof`.
    /// The contents of `buf` are unspecified in this case.
    ///
    /// If any other read error is encountered then this function immediately
    /// returns. The contents of `buf` are unspecified in this case.
    ///
    /// If this function returns an error, it is unspecified how many bytes it
    /// has read, but it will never read more than would be necessary to
    /// completely fill the buffer.
    /// ```
    fn read_exact(&mut self, mut buf: &mut [u8]) -> Result<(), Self::Error> {
        while !buf.is_empty() {
            match self.read(buf) {
                Ok(0) => break,
                Ok(n) => { let tmp = buf; buf = &mut tmp[n..]; }
                Err(ref e) if e.is_interrupted() => {}
                Err(e) => return Err(e),
            }
        }
        if !buf.is_empty() {
            Err(Self::Error::unexpected_eof("failed to fill whole buffer"))
        } else {
            Ok(())
        }
    }

    /// Creates a "by reference" adaptor for this instance of `Read`.
    ///
    /// The returned adaptor also implements `Read` and will simply borrow this
    /// current reader.
    fn by_ref(&mut self) -> &mut Self where Self: Sized { self }

    /// Transforms this `Read` instance to an `Iterator` over its bytes.
    ///
    /// The returned type implements `Iterator` where the `Item` is `Result<u8,
    /// R::Err>`.  The yielded item is `Ok` if a byte was successfully read and
    /// `Err` otherwise for I/O errors. EOF is mapped to returning `None` from
    /// this iterator.
    fn bytes(self) -> Bytes<Self> where Self: Sized {
        Bytes { inner: self }
    }

    /// Transforms this `Read` instance to an `Iterator` over `char`s.
    ///
    /// This adaptor will attempt to interpret this reader as a UTF-8 encoded
    /// sequence of characters. The returned iterator will return `None` once
    /// EOF is reached for this reader. Otherwise each element yielded will be a
    /// `Result<char, E>` where `E` may contain information about what I/O error
    /// occurred or where decoding failed.
    ///
    /// Currently this adaptor will discard intermediate data read, and should
    /// be avoided if this is not desired.
    fn chars(self) -> Chars<Self> where Self: Sized {
        Chars { inner: self }
    }

    /// Creates an adaptor which will chain this stream with another.
    ///
    /// The returned `Read` instance will first read all bytes from this object
    /// until EOF is encountered. Afterwards the output is equivalent to the
    /// output of `next`.
    fn chain<R: Read>(self, next: R) -> Chain<Self, R> where Self: Sized {
        Chain { first: self, second: next, done_first: false }
    }

    /// Creates an adaptor which will read at most `limit` bytes from it.
    ///
    /// This function returns a new instance of `Read` which will read at most
    /// `limit` bytes, after which it will always return EOF (`Ok(0)`). Any
    /// read errors will not count towards the number of bytes read and future
    /// calls to `read` may succeed.
    fn take(self, limit: u64) -> Take<Self> where Self: Sized {
        Take { inner: self, limit: limit }
    }
}

/// A trait for objects which are byte-oriented sinks.
///
/// Implementors of the `Write` trait are sometimes called 'writers'.
///
/// Writers are defined by two required methods, [`write()`] and [`flush()`]:
///
/// * The [`write()`] method will attempt to write some data into the object,
///   returning how many bytes were successfully written.
///
/// * The [`flush()`] method is useful for adaptors and explicit buffers
///   themselves for ensuring that all buffered data has been pushed out to the
///   'true sink'.
///
/// Writers are intended to be composable with one another. Many implementors
/// throughout [`std::io`] take and provide types which implement the `Write`
/// trait.
///
/// [`write()`]: #tymethod.write
/// [`flush()`]: #tymethod.flush
/// [`std::io`]: index.html
pub trait Write {
    /// All `Write` impls will need to supply an error type.
    /// The `std` types will automatically supply `std::io::Error`
    type Error: Error;
    /// Write a buffer into this object, returning how many bytes were written.
    ///
    /// This function will attempt to write the entire contents of `buf`, but
    /// the entire write may not succeed, or the write may also generate an
    /// error. A call to `write` represents *at most one* attempt to write to
    /// any wrapped object.
    ///
    /// Calls to `write` are not guaranteed to block waiting for data to be
    /// written, and a write which would otherwise block can be indicated through
    /// an `Err` variant.
    ///
    /// If the return value is `Ok(n)` then it must be guaranteed that
    /// `0 <= n <= buf.len()`. A return value of `0` typically means that the
    /// underlying object is no longer able to accept bytes and will likely not
    /// be able to in the future as well, or that the buffer provided is empty.
    ///
    /// # Errors
    ///
    /// Each call to `write` may generate an I/O error indicating that the
    /// operation could not be completed. If an error is returned then no bytes
    /// in the buffer were written to this writer.
    ///
    /// It is **not** considered an error if the entire buffer could not be
    /// written to this writer.
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error>;

    /// Flush this output stream, ensuring that all intermediately buffered
    /// contents reach their destination.
    ///
    /// # Errors
    ///
    /// It is considered an error if not all bytes could be written due to
    /// I/O errors or EOF being reached.
    fn flush(&mut self) -> Result<(), Self::Error>;

    /// Attempts to write an entire buffer into this write.
    ///
    /// This method will continuously call `write` while there is more data to
    /// write. This method will not return until the entire buffer has been
    /// successfully written or an error occurs. The first error generated from
    /// this method will be returned.
    ///
    /// # Errors
    ///
    /// This function will return the first error that `write` returns.
    fn write_all(&mut self, mut buf: &[u8]) -> Result<(), Self::Error> {
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => return Err(Self::Error::write_zero("failed to write whole buffer")),
                Ok(n) => buf = &buf[n..],
                Err(ref e) if e.is_interrupted() => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Writes a formatted string into this writer, returning any error
    /// encountered.
    ///
    /// This method is primarily used to interface with the
    /// [`format_args!`][formatargs] macro, but it is rare that this should
    /// explicitly be called. The [`write!`][write] macro should be favored to
    /// invoke this method instead.
    ///
    /// [formatargs]: ../macro.format_args.html
    /// [write]: ../macro.write.html
    ///
    /// This function internally uses the [`write_all`][writeall] method on
    /// this trait and hence will continuously write data so long as no errors
    /// are received. This also means that partial writes are not indicated in
    /// this signature.
    ///
    /// [writeall]: #method.write_all
    ///
    /// # Errors
    ///
    /// This function will return any I/O error reported while formatting.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::prelude::*;
    /// use std::fs::File;
    ///
    /// # fn foo() -> std::io::Result<()> {
    /// let mut buffer = try!(File::create("foo.txt"));
    ///
    /// // this call
    /// try!(write!(buffer, "{:.*}", 2, 1.234567));
    /// // turns into this:
    /// try!(buffer.write_fmt(format_args!("{:.*}", 2, 1.234567)));
    /// # Ok(())
    /// # }
    /// ```
    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), Self::Error> {
        // Create a shim which translates a Write to a fmt::Write and saves
        // off I/O errors. instead of discarding them
        struct Adaptor<'a, T: Write + ?Sized + 'a> {
            inner: &'a mut T,
            error: Result<(), T::Error>,
        }

        impl<'a, T: Write + ?Sized> fmt::Write for Adaptor<'a, T> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                match self.inner.write_all(s.as_bytes()) {
                    Ok(()) => Ok(()),
                    Err(e) => {
                        self.error = Err(e);
                        Err(fmt::Error)
                    }
                }
            }
        }

        let mut output = Adaptor { inner: self, error: Ok(()) };
        match fmt::write(&mut output, fmt) {
            Ok(()) => Ok(()),
            Err(fmt::Error) => {
                // check if the error came from the underlying `Write` or not
                if output.error.is_err() {
                    output.error
                } else {
                    Err(Error::other("formatter error"))
                }
            }
        }
    }

    /// Creates a "by reference" adaptor for this instance of `Write`.
    ///
    /// The returned adaptor also implements `Write` and will simply borrow this
    /// current writer.
    fn by_ref(&mut self) -> &mut Self where Self: Sized { self }
}

/// The `Seek` trait provides a cursor which can be moved within a stream of
/// bytes.
///
/// The stream typically has a fixed size, allowing seeking relative to either
/// end or the current offset.
pub trait Seek {
    /// All `Seek` impls will need to supply an error type.
    /// The `std` types will automatically supply `std::io::Error`
    type Error;
    /// Seek to an offset, in bytes, in a stream.
    ///
    /// A seek beyond the end of a stream is allowed, but implementation
    /// defined.
    ///
    /// If the seek operation completed successfully,
    /// this method returns the new position from the start of the stream.
    /// That position can be used later with [`SeekFrom::Start`].
    ///
    /// # Errors
    ///
    /// Seeking to a negative offset is considered an error.
    ///
    /// [`SeekFrom::Start`]: enum.SeekFrom.html#variant.Start
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error>;
}

/// Enumeration of possible methods to seek within an I/O object.
///
/// It is used by the [`Seek`] trait.
///
/// [`Seek`]: trait.Seek.html
#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum SeekFrom {
    /// Set the offset to the provided number of bytes.
    Start(u64),

    /// Set the offset to the size of this object plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    End(i64),

    /// Set the offset to the current position plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    Current(i64),
}

/// A `BufRead` is a type of `Read`er which has an internal buffer, allowing it
/// to perform extra ways of reading.
///
/// For example, reading line-by-line is inefficient without using a buffer, so
/// if you want to read by line, you'll need `BufRead`, which includes a
/// [`read_line()`] method as well as a [`lines()`] iterator.
///
pub trait BufRead: Read {
    /// Fills the internal buffer of this object, returning the buffer contents.
    ///
    /// This function is a lower-level call. It needs to be paired with the
    /// [`consume()`] method to function properly. When calling this
    /// method, none of the contents will be "read" in the sense that later
    /// calling `read` may return the same contents. As such, [`consume()`] must
    /// be called with the number of bytes that are consumed from this buffer to
    /// ensure that the bytes are never returned twice.
    ///
    /// [`consume()`]: #tymethod.consume
    ///
    /// An empty buffer returned indicates that the stream has reached EOF.
    ///
    /// # Errors
    ///
    /// This function will return an I/O error if the underlying reader was
    /// read, but returned an error.
    ///
    fn fill_buf(&mut self) -> Result<&[u8], <Self as Read>::Error>;

    /// Tells this buffer that `amt` bytes have been consumed from the buffer,
    /// so they should no longer be returned in calls to `read`.
    ///
    /// This function is a lower-level call. It needs to be paired with the
    /// [`fill_buf()`] method to function properly. This function does
    /// not perform any I/O, it simply informs this object that some amount of
    /// its buffer, returned from [`fill_buf()`], has been consumed and should
    /// no longer be returned. As such, this function may do odd things if
    /// [`fill_buf()`] isn't called before calling it.
    ///
    /// The `amt` must be `<=` the number of bytes in the buffer returned by
    /// [`fill_buf()`].
    ///
    /// # Examples
    ///
    /// Since `consume()` is meant to be used with [`fill_buf()`],
    /// that method's example includes an example of `consume()`.
    ///
    /// [`fill_buf()`]: #tymethod.fill_buf
    fn consume(&mut self, amt: usize);
}

/// Adaptor to chain together two readers.
///
/// This struct is generally created by calling [`chain()`] on a reader.
/// Please see the documentation of [`chain()`] for more details.
///
/// [`chain()`]: trait.Read.html#method.chain
#[derive(Debug)]
pub struct Chain<T, U> {
    first: T,
    second: U,
    done_first: bool,
}

impl<E: Error, T: Read<Error = E>, U: Read<Error = E>> Read for Chain<T, U> {
    type Error = E;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, E> {
        if !self.done_first {
            match self.first.read(buf)? {
                0 if buf.len() != 0 => { self.done_first = true; }
                n => return Ok(n),
            }
        }
        self.second.read(buf)
    }
}

impl<
    E: Error,
    T: BufRead + Read<Error = E>,
    U: BufRead + Read<Error = E>,
> BufRead for Chain<T, U> {
    fn fill_buf(&mut self) -> Result<&[u8], E> {
        if !self.done_first {
            match self.first.fill_buf()? {
                buf if buf.len() == 0 => { self.done_first = true; }
                buf => return Ok(buf),
            }
        }
        self.second.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        if !self.done_first {
            self.first.consume(amt)
        } else {
            self.second.consume(amt)
        }
    }
}

/// Reader adaptor which limits the bytes read from an underlying reader.
///
/// This struct is generally created by calling [`take()`] on a reader.
/// Please see the documentation of [`take()`] for more details.
///
/// [`take()`]: trait.Read.html#method.take
#[derive(Debug)]
pub struct Take<T> {
    inner: T,
    limit: u64,
}

impl<T> Take<T> {
    /// Returns the number of bytes that can be read before this instance will
    /// return EOF.
    ///
    /// # Note
    ///
    /// This instance may reach `EOF` after reading fewer bytes than indicated by
    /// this method if the underlying [`Read`] instance reaches EOF.
    ///
    /// [`Read`]: ../../std/io/trait.Read.html
    pub fn limit(&self) -> u64 { self.limit }

    /// Consumes the `Take`, returning the wrapped reader.
    pub fn into_inner(self) -> T {
        self.inner
    }
}

impl<E: Error, T: Read<Error = E>> Read for Take<T> {
    type Error = E;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, E> {
        // Don't call into inner reader at all at EOF because it may still block
        if self.limit == 0 {
            return Ok(0);
        }

        let max = cmp::min(buf.len() as u64, self.limit) as usize;
        let n = self.inner.read(&mut buf[..max])?;
        self.limit -= n as u64;
        Ok(n)
    }
}

impl<T: BufRead> BufRead for Take<T> {
    fn fill_buf(&mut self) -> Result<&[u8], T::Error> {
        // Don't call into inner reader at all at EOF because it may still block
        if self.limit == 0 {
            return Ok(&[]);
        }

        let buf = self.inner.fill_buf()?;
        let cap = cmp::min(buf.len() as u64, self.limit) as usize;
        Ok(&buf[..cap])
    }

    fn consume(&mut self, amt: usize) {
        // Don't let callers reset the limit by passing an overlarge value
        let amt = cmp::min(amt as u64, self.limit) as usize;
        self.limit -= amt as u64;
        self.inner.consume(amt);
    }
}

fn read_one_byte<E: Error, R: Read<Error= E>>(reader: &mut R) -> Option<Result<u8, E>> {
    let mut buf = [0];
    loop {
        return match reader.read(&mut buf) {
            Ok(0) => None,
            Ok(..) => Some(Ok(buf[0])),
            Err(ref e) if e.is_interrupted() => continue,
            Err(e) => Some(Err(e)),
        };
    }
}

/// An iterator over `u8` values of a reader.
///
/// This struct is generally created by calling [`bytes()`] on a reader.
/// Please see the documentation of [`bytes()`] for more details.
///
/// [`bytes()`]: trait.Read.html#method.bytes
#[derive(Debug)]
pub struct Bytes<R> {
    inner: R,
}

impl<E: Error, R: Read<Error = E>> Iterator for Bytes<R> {
    type Item = Result<u8, E>;

    fn next(&mut self) -> Option<Result<u8, E>> {
        read_one_byte(&mut self.inner)
    }
}

/// An iterator over the `char`s of a reader.
///
/// This struct is generally created by calling [`chars()`][chars] on a reader.
/// Please see the documentation of `chars()` for more details.
///
/// [chars]: trait.Read.html#method.chars
#[derive(Debug)]
pub struct Chars<R> {
    inner: R,
}

/// An enumeration of possible errors that can be generated from the `Chars`
/// adapter.
#[derive(Debug)]
pub enum CharsError<E: Error> {
    /// Variant representing that the underlying stream was read successfully
    /// but it did not contain valid utf8 data.
    NotUtf8,

    /// Variant representing that an I/O error occurred.
    Other(E),
}

impl<E: Error, R: Read<Error = E>> Iterator for Chars<R> {
    type Item = Result<char, CharsError<E>>;

    fn next(&mut self) -> Option<result::Result<char, CharsError<E>>> {
        let first_byte = match read_one_byte(&mut self.inner) {
            None => return None,
            Some(Ok(b)) => b,
            Some(Err(e)) => return Some(Err(CharsError::Other(e))),
        };
        let width = ::str::utf8_char_width(first_byte);
        if width == 1 { return Some(Ok(first_byte as char)) }
        if width == 0 { return Some(Err(CharsError::NotUtf8)) }
        let mut buf = [first_byte, 0, 0, 0];
        {
            let mut start = 1;
            while start < width {
                match self.inner.read(&mut buf[start..width]) {
                    Ok(0) => return Some(Err(CharsError::NotUtf8)),
                    Ok(n) => start += n,
                    Err(ref e) if e.is_interrupted() => continue,
                    Err(e) => return Some(Err(CharsError::Other(e))),
                }
            }
        }
        Some(match core::str::from_utf8(&buf[..width]).ok() {
            Some(s) => Ok(s.chars().next().unwrap()),
            None => Err(CharsError::NotUtf8),
        })
    }
}
