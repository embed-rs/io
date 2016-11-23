// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Buffering wrappers for I/O traits

use prelude::*;

use core::cmp;
use core::fmt;
use ::{Error, SeekFrom};
use impls::{FailedToFillWholeBuffer, FailedToWriteWholeBuffer, Forward};
use memchr::memrchr;

/// The `BufReader` struct adds buffering to any reader.
///
/// It can be excessively inefficient to work directly with a [`Read`] instance.
/// For example, every call to [`read`] on [`TcpStream`] results in a system call.
/// A `BufReader` performs large, infrequent reads on the underlying [`Read`]
/// and maintains an in-memory buffer of the results.
///
/// [`Read`]: ../../std/io/trait.Read.html
/// [`read`]: ../../std/net/struct.TcpStream.html#method.read
/// [`TcpStream`]: ../../std/net/struct.TcpStream.html
///
/// # Examples
///
/// ```
/// use std::io::prelude::*;
/// use std::io::BufReader;
/// use std::fs::File;
///
/// # fn foo() -> std::io::Result<()> {
/// let mut f = try!(File::open("log.txt"));
/// let mut reader = BufReader::new(f);
///
/// let mut line = String::new();
/// let len = try!(reader.read_line(&mut line));
/// println!("First line is {} bytes long", len);
/// # Ok(())
/// # }
/// ```
pub struct BufReader<R, B> {
    inner: R,
    buf: B,
    pos: usize,
    cap: usize,
}

impl<R: Read, B: AsMut<[u8]>> BufReader<R, B> {
    /// Creates a new `BufReader` with the given buffer
    pub fn new_preallocated(inner: R, buf: B) -> BufReader<R, B> {
        BufReader {
            inner: inner,
            buf: buf,
            pos: 0,
            cap: 0,
        }
    }

    /// Gets a reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    pub fn get_ref(&self) -> &R { &self.inner }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    pub fn get_mut(&mut self) -> &mut R { &mut self.inner }

    /// Unwraps this `BufReader`, returning the underlying reader.
    ///
    /// Note that any leftover data in the internal buffer is lost.
    pub fn into_inner(self) -> R { self.inner }
}

impl<B: AsMut<[u8]>, R: Read> Read for BufReader<R, B> {
    type Error = R::Error;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, R::Error> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if self.pos == self.cap && buf.len() >= self.buf.as_mut().len() {
            return self.inner.read(buf);
        }
        let nread = {
            let mut rem = Forward(self.fill_buf()?);
            rem.read(buf).map_err(|_: FailedToFillWholeBuffer| {
                R::Error::unexpected_eof("failed to fill whole buffer")
            })?
        };
        self.consume(nread);
        Ok(nread)
    }
}

impl<B: AsMut<[u8]>, R: Read> BufRead for BufReader<R, B> {
    fn fill_buf(&mut self) -> Result<&[u8], R::Error> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.
        if self.pos >= self.cap {
            debug_assert!(self.pos == self.cap);
            self.cap = self.inner.read(self.buf.as_mut())?;
            self.pos = 0;
        }
        Ok(&self.buf.as_mut()[self.pos..self.cap])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = cmp::min(self.pos + amt, self.cap);
    }
}

impl<B: AsRef<[u8]>, R> fmt::Debug for BufReader<R, B> where R: fmt::Debug {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BufReader")
            .field("reader", &self.inner)
            .field("buffer", &format_args!("{}/{}", self.cap - self.pos, self.buf.as_ref().len()))
            .finish()
    }
}

impl<B, R: Seek> Seek for BufReader<R, B> {
    type Error = R::Error;
    /// Seek to an offset, in bytes, in the underlying reader.
    ///
    /// The position used for seeking with `SeekFrom::Current(_)` is the
    /// position the underlying reader would be at if the `BufReader` had no
    /// internal buffer.
    ///
    /// Seeking always discards the internal buffer, even if the seek position
    /// would otherwise fall within it. This guarantees that calling
    /// `.into_inner()` immediately after a seek yields the underlying reader
    /// at the same position.
    ///
    /// See `std::io::Seek` for more details.
    ///
    /// Note: In the edge case where you're seeking with `SeekFrom::Current(n)`
    /// where `n` minus the internal buffer length underflows an `i64`, two
    /// seeks will be performed instead of one. If the second seek returns
    /// `Err`, the underlying reader will be left at the same position it would
    /// have if you seeked to `SeekFrom::Current(0)`.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, R::Error> {
        let result: u64;
        if let SeekFrom::Current(n) = pos {
            let remainder = (self.cap - self.pos) as i64;
            // it should be safe to assume that remainder fits within an i64 as the alternative
            // means we managed to allocate 8 exbibytes and that's absurd.
            // But it's not out of the realm of possibility for some weird underlying reader to
            // support seeking by i64::min_value() so we need to handle underflow when subtracting
            // remainder.
            if let Some(offset) = n.checked_sub(remainder) {
                result = self.inner.seek(SeekFrom::Current(offset))?;
            } else {
                // seek backwards by our remainder, and then by the offset
                self.inner.seek(SeekFrom::Current(-remainder))?;
                self.pos = self.cap; // empty the buffer
                result = self.inner.seek(SeekFrom::Current(n))?;
            }
        } else {
            // Seeking with Start/End doesn't care about our buffer length.
            result = self.inner.seek(pos)?;
        }
        self.pos = self.cap; // empty the buffer
        Ok(result)
    }
}

/// Wraps a writer and buffers its output.
///
/// It can be excessively inefficient to work directly with something that
/// implements [`Write`]. For example, every call to [`write`] on [`TcpStream`]
/// results in a system call. A `BufWriter` keeps an in-memory buffer of data
/// and writes it to an underlying writer in large, infrequent batches.
///
/// The buffer will be written out when the writer is dropped.
///
/// # Examples
///
/// Let's write the numbers one through ten to a [`TcpStream`]:
///
/// ```no_run
/// use std::io::prelude::*;
/// use std::net::TcpStream;
///
/// let mut stream = TcpStream::connect("127.0.0.1:34254").unwrap();
///
/// for i in 1..10 {
///     stream.write(&[i]).unwrap();
/// }
/// ```
///
/// Because we're not buffering, we write each one in turn, incurring the
/// overhead of a system call per byte written. We can fix this with a
/// `BufWriter`:
///
/// ```no_run
/// use std::io::prelude::*;
/// use std::io::BufWriter;
/// use std::net::TcpStream;
///
/// let mut stream = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
///
/// for i in 1..10 {
///     stream.write(&[i]).unwrap();
/// }
/// ```
///
/// By wrapping the stream with a `BufWriter`, these ten writes are all grouped
/// together by the buffer, and will all be written out in one system call when
/// the `stream` is dropped.
///
/// [`Write`]: ../../std/io/trait.Write.html
/// [`write`]: ../../std/net/struct.TcpStream.html#method.write
/// [`TcpStream`]: ../../std/net/struct.TcpStream.html
pub struct BufWriter<W: Write, B: AsMut<[u8]> + AsRef<[u8]>> {
    inner: Option<W>,
    buf: B,
    len: usize,
    // #30888: If the inner writer panics in a call to write, we don't want to
    // write the buffered data a second time in BufWriter's destructor. This
    // flag tells the Drop impl if it should skip the flush.
    panicked: bool,
}

/// An error returned by `into_inner` which combines an error that
/// happened while writing out the buffer, and the buffered writer object
/// which may be used to recover from the condition.
///
/// # Examples
///
/// ```no_run
/// use std::io::BufWriter;
/// use std::net::TcpStream;
///
/// let mut stream = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
///
/// // do stuff with the stream
///
/// // we want to get our `TcpStream` back, so let's try:
///
/// let stream = match stream.into_inner() {
///     Ok(s) => s,
///     Err(e) => {
///         // Here, e is an IntoInnerError
///         panic!("An error occurred");
///     }
/// };
/// ```
#[derive(Debug)]
pub struct IntoInnerError<W, E: Error>(W, E);

impl<W: Write, B: AsMut<[u8]> + AsRef<[u8]>> BufWriter<W, B> {
    /// Creates a new `BufWriter` with a default buffer capacity.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufWriter;
    /// use std::net::TcpStream;
    ///
    /// let mut buffer = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
    /// ```
    pub fn new_preallocated(inner: W, buf: B) -> Self {
        BufWriter {
            inner: Some(inner),
            buf: buf,
            panicked: false,
            len: 0,
        }
    }

    fn flush_buf(&mut self) -> Result<(), W::Error> {
        let mut written = 0;
        let mut ret = Ok(());
        while written < self.len {
            self.panicked = true;
            let r = self.inner.as_mut().unwrap().write(&self.buf.as_mut()[written..]);
            self.panicked = false;

            match r {
                Ok(0) => {
                    ret = Err(W::Error::write_zero("failed to write the buffered data"));
                    break;
                }
                Ok(n) => written += n,
                Err(ref e) if e.is_interrupted() => {}
                Err(e) => { ret = Err(e); break }

            }
        }
        if written > 0 {
            if written == self.len {
                self.len = 0;
            } else {
                let buf = self.buf.as_mut();
                for i in 0..(self.len - written) {
                    buf[i] = buf[i + written];
                }
                self.len -= written;
            }
        }
        ret
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufWriter;
    /// use std::net::TcpStream;
    ///
    /// let mut buffer = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
    ///
    /// // we can use reference just like buffer
    /// let reference = buffer.get_ref();
    /// ```
    pub fn get_ref(&self) -> &W { self.inner.as_ref().unwrap() }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufWriter;
    /// use std::net::TcpStream;
    ///
    /// let mut buffer = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
    ///
    /// // we can use reference just like buffer
    /// let reference = buffer.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut W { self.inner.as_mut().unwrap() }

    /// Unwraps this `BufWriter`, returning the underlying writer.
    ///
    /// The buffer is written out before returning the writer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufWriter;
    /// use std::net::TcpStream;
    ///
    /// let mut buffer = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
    ///
    /// // unwrap the TcpStream and flush the buffer
    /// let stream = buffer.into_inner().unwrap();
    /// ```
    pub fn into_inner(mut self) -> Result<W, IntoInnerError<BufWriter<W, B>, W::Error>> {
        match self.flush_buf() {
            Err(e) => Err(IntoInnerError(self, e)),
            Ok(()) => Ok(self.inner.take().unwrap())
        }
    }
}

impl<B: AsMut<[u8]> + AsRef<[u8]>, W: Write> Write for BufWriter<W, B> {
    type Error = W::Error;
    fn write(&mut self, buf: &[u8]) -> Result<usize, W::Error> {
        if buf.len() + self.len > self.buf.as_mut().len() {
            self.flush_buf()?;
        }
        if buf.len() >= self.buf.as_mut().len() {
            self.panicked = true;
            let r = self.inner.as_mut().unwrap().write(buf);
            self.panicked = false;
            r
        } else {
            let map = |_: FailedToWriteWholeBuffer| {
                W::Error::write_zero("failed to write whole buffer")
            };
            Write::write(&mut Forward(&mut self.buf.as_mut()[..self.len]), buf).map_err(map)
        }
    }
    fn flush(&mut self) -> Result<(), W::Error> {
        self.flush_buf().and_then(|()| self.get_mut().flush())
    }
}

impl<B: AsMut<[u8]> + AsRef<[u8]>, W: Write> fmt::Debug for BufWriter<W, B> where W: fmt::Debug {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BufWriter")
            .field("writer", &self.inner.as_ref().unwrap())
            .field("buffer", &format_args!("{}/{}", self.len, self.buf.as_ref().len()))
            .finish()
    }
}

impl<B: AsMut<[u8]> + AsRef<[u8]>, E: Error, W: Write<Error = E> + Seek<Error = E>> Seek for BufWriter<W, B> {
    type Error = E;
    /// Seek to the offset, in bytes, in the underlying writer.
    ///
    /// Seeking always writes out the internal buffer before seeking.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, E> {
        self.flush_buf().and_then(|_| self.get_mut().seek(pos))
    }
}

impl<B: AsMut<[u8]> + AsRef<[u8]>, W: Write> Drop for BufWriter<W, B> {
    fn drop(&mut self) {
        if self.inner.is_some() && !self.panicked {
            // dtors should not panic, so we ignore a failed flush
            let _r = self.flush_buf();
        }
    }
}

impl<W, E: Error> IntoInnerError<W, E> {
    /// Returns the error which caused the call to `into_inner()` to fail.
    ///
    /// This error was returned when attempting to write the internal buffer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufWriter;
    /// use std::net::TcpStream;
    ///
    /// let mut stream = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
    ///
    /// // do stuff with the stream
    ///
    /// // we want to get our `TcpStream` back, so let's try:
    ///
    /// let stream = match stream.into_inner() {
    ///     Ok(s) => s,
    ///     Err(e) => {
    ///         // Here, e is an IntoInnerError, let's log the inner error.
    ///         //
    ///         // We'll just 'log' to stdout for this example.
    ///         println!("{}", e.error());
    ///
    ///         panic!("An unexpected error occurred.");
    ///     }
    /// };
    /// ```
    pub fn error(&self) -> &E { &self.1 }

    /// Returns the buffered writer instance which generated the error.
    ///
    /// The returned object can be used for error recovery, such as
    /// re-inspecting the buffer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufWriter;
    /// use std::net::TcpStream;
    ///
    /// let mut stream = BufWriter::new(TcpStream::connect("127.0.0.1:34254").unwrap());
    ///
    /// // do stuff with the stream
    ///
    /// // we want to get our `TcpStream` back, so let's try:
    ///
    /// let stream = match stream.into_inner() {
    ///     Ok(s) => s,
    ///     Err(e) => {
    ///         // Here, e is an IntoInnerError, let's re-examine the buffer:
    ///         let buffer = e.into_inner();
    ///
    ///         // do stuff to try to recover
    ///
    ///         // afterwards, let's just return the stream
    ///         buffer.into_inner().unwrap()
    ///     }
    /// };
    /// ```
    pub fn into_inner(self) -> W { self.0 }
}

impl<E: Error + fmt::Display, W> fmt::Display for IntoInnerError<W, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.error().fmt(f)
    }
}

/// Wraps a writer and buffers output to it, flushing whenever a newline
/// (`0x0a`, `'\n'`) is detected.
///
/// The [`BufWriter`][bufwriter] struct wraps a writer and buffers its output.
/// But it only does this batched write when it goes out of scope, or when the
/// internal buffer is full. Sometimes, you'd prefer to write each line as it's
/// completed, rather than the entire buffer at once. Enter `LineWriter`. It
/// does exactly that.
///
/// [bufwriter]: struct.BufWriter.html
///
/// If there's still a partial line in the buffer when the `LineWriter` is
/// dropped, it will flush those contents.
///
/// # Examples
///
/// We can use `LineWriter` to write one line at a time, significantly
/// reducing the number of actual writes to the file.
///
/// ```
/// use std::fs::File;
/// use std::io::prelude::*;
/// use std::io::LineWriter;
///
/// # fn foo() -> std::io::Result<()> {
/// let road_not_taken = b"I shall be telling this with a sigh
/// Somewhere ages and ages hence:
/// Two roads diverged in a wood, and I -
/// I took the one less traveled by,
/// And that has made all the difference.";
///
/// let file = try!(File::create("poem.txt"));
/// let mut file = LineWriter::new(file);
///
/// for &byte in road_not_taken.iter() {
///    file.write(&[byte]).unwrap();
/// }
///
/// // let's check we did the right thing.
/// let mut file = try!(File::open("poem.txt"));
/// let mut contents = String::new();
///
/// try!(file.read_to_string(&mut contents));
///
/// assert_eq!(contents.as_bytes(), &road_not_taken[..]);
/// # Ok(())
/// # }
/// ```
pub struct LineWriter<W: Write, B: AsMut<[u8]> + AsRef<[u8]>> {
    inner: BufWriter<W, B>,
}

impl<W: Write, B: AsMut<[u8]> + AsRef<[u8]>> LineWriter<W, B> {
    /// Creates a new `LineWriter`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// # fn foo() -> std::io::Result<()> {
    /// let file = try!(File::create("poem.txt"));
    /// let file = LineWriter::new(file);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new_preallocated(inner: W, buf: B) -> LineWriter<W, B> {
        LineWriter { inner: BufWriter::new_preallocated(inner, buf) }
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// # fn foo() -> std::io::Result<()> {
    /// let file = try!(File::create("poem.txt"));
    /// let file = LineWriter::new(file);
    ///
    /// let reference = file.get_ref();
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_ref(&self) -> &W { self.inner.get_ref() }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// Caution must be taken when calling methods on the mutable reference
    /// returned as extra writes could corrupt the output stream.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// # fn foo() -> std::io::Result<()> {
    /// let file = try!(File::create("poem.txt"));
    /// let mut file = LineWriter::new(file);
    ///
    /// // we can use reference just like file
    /// let reference = file.get_mut();
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_mut(&mut self) -> &mut W { self.inner.get_mut() }

    /// Unwraps this `LineWriter`, returning the underlying writer.
    ///
    /// The internal buffer is written out before returning the writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// # fn foo() -> std::io::Result<()> {
    /// let file = try!(File::create("poem.txt"));
    ///
    /// let writer: LineWriter<File> = LineWriter::new(file);
    ///
    /// let file: File = try!(writer.into_inner());
    /// # Ok(())
    /// # }
    /// ```
    pub fn into_inner(self) -> Result<W, IntoInnerError<LineWriter<W, B>, W::Error>> {
        self.inner.into_inner().map_err(|IntoInnerError(buf, e)| {
            IntoInnerError(LineWriter { inner: buf }, e)
        })
    }
}

impl<B: AsMut<[u8]> + AsRef<[u8]>, W: Write> Write for LineWriter<W, B> {
    type Error = W::Error;
    fn write(&mut self, buf: &[u8]) -> Result<usize, W::Error> {
        match memrchr(b'\n', buf) {
            Some(i) => {
                let n = self.inner.write(&buf[..i + 1])?;
                if n != i + 1 || self.inner.flush().is_err() {
                    // Do not return errors on partial writes.
                    return Ok(n);
                }
                self.inner.write(&buf[i + 1..]).map(|i| n + i)
            }
            None => self.inner.write(buf),
        }
    }

    fn flush(&mut self) -> Result<(), W::Error> { self.inner.flush() }
}

impl<B: AsMut<[u8]> + AsRef<[u8]>, W: Write> fmt::Debug for LineWriter<W, B> where W: fmt::Debug {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("LineWriter")
            .field("writer", &self.inner.inner)
            .field("buffer",
                   &format_args!("{}/{}", self.inner.len, self.inner.buf.as_ref().len()))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use io::prelude::*;
    use io::{self, BufReader, BufWriter, LineWriter, SeekFrom};
    use sync::atomic::{AtomicUsize, Ordering};
    use thread;
    use test;

    /// A dummy reader intended at testing short-reads propagation.
    pub struct ShortReader {
        lengths: Vec<usize>,
    }

    impl Read for ShortReader {
        fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
            if self.lengths.is_empty() {
                Ok(0)
            } else {
                Ok(self.lengths.remove(0))
            }
        }
    }

    #[test]
    fn test_buffered_reader() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(2, inner);

        let mut buf = [0, 0, 0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 3);
        let b: &[_] = &[5, 6, 7];
        assert_eq!(buf, b);

        let mut buf = [0, 0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 2);
        let b: &[_] = &[0, 1];
        assert_eq!(buf, b);

        let mut buf = [0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 1);
        let b: &[_] = &[2];
        assert_eq!(buf, b);

        let mut buf = [0, 0, 0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 1);
        let b: &[_] = &[3, 0, 0];
        assert_eq!(buf, b);

        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 1);
        let b: &[_] = &[4, 0, 0];
        assert_eq!(buf, b);

        assert_eq!(reader.read(&mut buf).unwrap(), 0);
    }

    #[test]
    fn test_buffered_reader_seek() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(2, io::Cursor::new(inner));

        assert_eq!(reader.seek(SeekFrom::Start(3)).ok(), Some(3));
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(3));
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert_eq!(reader.seek(SeekFrom::Current(1)).ok(), Some(4));
        assert_eq!(reader.fill_buf().ok(), Some(&[1, 2][..]));
        reader.consume(1);
        assert_eq!(reader.seek(SeekFrom::Current(-2)).ok(), Some(3));
    }

    #[test]
    fn test_buffered_reader_seek_underflow() {
        // gimmick reader that yields its position modulo 256 for each byte
        struct PositionReader {
            pos: u64
        }
        impl Read for PositionReader {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                let len = buf.len();
                for x in buf {
                    *x = self.pos as u8;
                    self.pos = self.pos.wrapping_add(1);
                }
                Ok(len)
            }
        }
        impl Seek for PositionReader {
            fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
                match pos {
                    SeekFrom::Start(n) => {
                        self.pos = n;
                    }
                    SeekFrom::Current(n) => {
                        self.pos = self.pos.wrapping_add(n as u64);
                    }
                    SeekFrom::End(n) => {
                        self.pos = u64::max_value().wrapping_add(n as u64);
                    }
                }
                Ok(self.pos)
            }
        }

        let mut reader = BufReader::with_capacity(5, PositionReader { pos: 0 });
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1, 2, 3, 4][..]));
        assert_eq!(reader.seek(SeekFrom::End(-5)).ok(), Some(u64::max_value()-5));
        assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
        // the following seek will require two underlying seeks
        let expected = 9223372036854775802;
        assert_eq!(reader.seek(SeekFrom::Current(i64::min_value())).ok(), Some(expected));
        assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
        // seeking to 0 should empty the buffer.
        assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(expected));
        assert_eq!(reader.get_ref().pos, expected);
    }

    #[test]
    fn test_buffered_writer() {
        let inner = Vec::new();
        let mut writer = BufWriter::with_capacity(2, inner);

        writer.write(&[0, 1]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1]);

        writer.write(&[2]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1]);

        writer.write(&[3]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1]);

        writer.flush().unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 2, 3]);

        writer.write(&[4]).unwrap();
        writer.write(&[5]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 2, 3]);

        writer.write(&[6]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 2, 3, 4, 5]);

        writer.write(&[7, 8]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 2, 3, 4, 5, 6, 7, 8]);

        writer.write(&[9, 10, 11]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);

        writer.flush().unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
    }

    #[test]
    fn test_buffered_writer_inner_flushes() {
        let mut w = BufWriter::with_capacity(3, Vec::new());
        w.write(&[0, 1]).unwrap();
        assert_eq!(*w.get_ref(), []);
        let w = w.into_inner().unwrap();
        assert_eq!(w, [0, 1]);
    }

    #[test]
    fn test_buffered_writer_seek() {
        let mut w = BufWriter::with_capacity(3, io::Cursor::new(Vec::new()));
        w.write_all(&[0, 1, 2, 3, 4, 5]).unwrap();
        w.write_all(&[6, 7]).unwrap();
        assert_eq!(w.seek(SeekFrom::Current(0)).ok(), Some(8));
        assert_eq!(&w.get_ref().get_ref()[..], &[0, 1, 2, 3, 4, 5, 6, 7][..]);
        assert_eq!(w.seek(SeekFrom::Start(2)).ok(), Some(2));
        w.write_all(&[8, 9]).unwrap();
        assert_eq!(&w.into_inner().unwrap().into_inner()[..], &[0, 1, 8, 9, 4, 5, 6, 7]);
    }

    #[test]
    fn test_read_until() {
        let inner: &[u8] = &[0, 1, 2, 1, 0];
        let mut reader = BufReader::with_capacity(2, inner);
        let mut v = Vec::new();
        reader.read_until(0, &mut v).unwrap();
        assert_eq!(v, [0]);
        v.truncate(0);
        reader.read_until(2, &mut v).unwrap();
        assert_eq!(v, [1, 2]);
        v.truncate(0);
        reader.read_until(1, &mut v).unwrap();
        assert_eq!(v, [1]);
        v.truncate(0);
        reader.read_until(8, &mut v).unwrap();
        assert_eq!(v, [0]);
        v.truncate(0);
        reader.read_until(9, &mut v).unwrap();
        assert_eq!(v, []);
    }

    #[test]
    fn test_line_buffer_fail_flush() {
        // Issue #32085
        struct FailFlushWriter<'a>(&'a mut Vec<u8>);

        impl<'a> Write for FailFlushWriter<'a> {
            fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
                self.0.extend_from_slice(buf);
                Ok(buf.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                Err(io::Error::new(io::ErrorKind::Other, "flush failed"))
            }
        }

        let mut buf = Vec::new();
        {
            let mut writer = LineWriter::new(FailFlushWriter(&mut buf));
            let to_write = b"abc\ndef";
            if let Ok(written) = writer.write(to_write) {
                assert!(written < to_write.len(), "didn't flush on new line");
                // PASS
                return;
            }
        }
        assert!(buf.is_empty(), "write returned an error but wrote data");
    }

    #[test]
    fn test_line_buffer() {
        let mut writer = LineWriter::new(Vec::new());
        writer.write(&[0]).unwrap();
        assert_eq!(*writer.get_ref(), []);
        writer.write(&[1]).unwrap();
        assert_eq!(*writer.get_ref(), []);
        writer.flush().unwrap();
        assert_eq!(*writer.get_ref(), [0, 1]);
        writer.write(&[0, b'\n', 1, b'\n', 2]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 0, b'\n', 1, b'\n']);
        writer.flush().unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 0, b'\n', 1, b'\n', 2]);
        writer.write(&[3, b'\n']).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 0, b'\n', 1, b'\n', 2, 3, b'\n']);
    }

    #[test]
    fn test_read_line() {
        let in_buf: &[u8] = b"a\nb\nc";
        let mut reader = BufReader::with_capacity(2, in_buf);
        let mut s = String::new();
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "a\n");
        s.truncate(0);
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "b\n");
        s.truncate(0);
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "c");
        s.truncate(0);
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "");
    }

    #[test]
    fn test_lines() {
        let in_buf: &[u8] = b"a\nb\nc";
        let reader = BufReader::with_capacity(2, in_buf);
        let mut it = reader.lines();
        assert_eq!(it.next().unwrap().unwrap(), "a".to_string());
        assert_eq!(it.next().unwrap().unwrap(), "b".to_string());
        assert_eq!(it.next().unwrap().unwrap(), "c".to_string());
        assert!(it.next().is_none());
    }

    #[test]
    fn test_short_reads() {
        let inner = ShortReader{lengths: vec![0, 1, 2, 0, 1, 0]};
        let mut reader = BufReader::new(inner);
        let mut buf = [0, 0];
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 1);
        assert_eq!(reader.read(&mut buf).unwrap(), 2);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 1);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
    }

    #[test]
    fn read_char_buffered() {
        let buf = [195, 159];
        let reader = BufReader::with_capacity(1, &buf[..]);
        assert_eq!(reader.chars().next().unwrap().unwrap(), 'ß');
    }

    #[test]
    fn test_chars() {
        let buf = [195, 159, b'a'];
        let reader = BufReader::with_capacity(1, &buf[..]);
        let mut it = reader.chars();
        assert_eq!(it.next().unwrap().unwrap(), 'ß');
        assert_eq!(it.next().unwrap().unwrap(), 'a');
        assert!(it.next().is_none());
    }

    #[test]
    #[should_panic]
    fn dont_panic_in_drop_on_panicked_flush() {
        struct FailFlushWriter;

        impl Write for FailFlushWriter {
            fn write(&mut self, buf: &[u8]) -> io::Result<usize> { Ok(buf.len()) }
            fn flush(&mut self) -> io::Result<()> {
                Err(io::Error::last_os_error())
            }
        }

        let writer = FailFlushWriter;
        let _writer = BufWriter::new(writer);

        // If writer panics *again* due to the flush error then the process will
        // abort.
        panic!();
    }

    #[test]
    #[cfg_attr(target_os = "emscripten", ignore)]
    fn panic_in_write_doesnt_flush_in_drop() {
        static WRITES: AtomicUsize = AtomicUsize::new(0);

        struct PanicWriter;

        impl Write for PanicWriter {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                WRITES.fetch_add(1, Ordering::SeqCst);
                panic!();
            }
            fn flush(&mut self) -> io::Result<()> { Ok(()) }
        }

        thread::spawn(|| {
            let mut writer = BufWriter::new(PanicWriter);
            let _ = writer.write(b"hello world");
            let _ = writer.flush();
        }).join().unwrap_err();

        assert_eq!(WRITES.load(Ordering::SeqCst), 1);
    }

    #[bench]
    fn bench_buffered_reader(b: &mut test::Bencher) {
        b.iter(|| {
            BufReader::new(io::empty())
        });
    }

    #[bench]
    fn bench_buffered_writer(b: &mut test::Bencher) {
        b.iter(|| {
            BufWriter::new(io::sink())
        });
    }
}
