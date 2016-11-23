// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::cmp;
use ::{SeekFrom, Read, Write, Seek, BufRead, Error};
use core::fmt;
use core::mem;

// =============================================================================
// Forwarding implementations


// FIXME: orphan impls don't allow implementing this and `std_impls` at the same time
// specialization + lattice rules required
/// Helper type to work around the issue that we can't implement `Read` for `&impl Read` and
/// `std::io::Read` for `&impl std::io::Read` in the presence of `impl Read for impl std::io::Read`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Forward<T, E: Error>(T, ::core::marker::PhantomData<E>);

impl<T, E: Error> Forward<T, E> {
    pub fn new(t: T) -> Self {
        Forward(t, ::core::marker::PhantomData)
    }
}

impl<T: PartialEq, E: Error> PartialEq<T> for Forward<T, E> {
    fn eq(&self, other: &T) -> bool {
        &self.0 == other
    }
}

impl<T, E: Error> ::core::ops::Deref for Forward<T, E> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T, E: Error> AsRef<T> for Forward<T, E> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T, E: Error> AsMut<T> for Forward<T, E> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<'a, R: Read + ?Sized> Read for Forward<&'a mut R, R::Error> {
    type Error = R::Error;
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, R::Error> {
        (*self.0).read(buf)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), R::Error> {
        (*self.0).read_exact(buf)
    }
}

impl<'a, W: Write + ?Sized> Write for Forward<&'a mut W, W::Error> {
    type Error = W::Error;
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, W::Error> { (*self.0).write(buf) }

    #[inline]
    fn flush(&mut self) -> Result<(), W::Error> { (*self.0).flush() }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> Result<(), W::Error> {
        (*self.0).write_all(buf)
    }

    #[inline]
    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), W::Error> {
        (*self.0).write_fmt(fmt)
    }
}

impl<'a, S: Seek + ?Sized> Seek for Forward<&'a mut S, S::Error> {
    type Error = S::Error;
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, S::Error> { (*self.0).seek(pos) }
}

impl<'a, B: BufRead + ?Sized> BufRead for Forward<&'a mut B, <B as Read>::Error> {
    #[inline]
    fn fill_buf(&mut self) -> Result<&[u8], <B as Read>::Error> { (*self.0).fill_buf() }

    #[inline]
    fn consume(&mut self, amt: usize) { (*self.0).consume(amt) }
}


// =============================================================================
// In-memory buffer implementations

/// Read is implemented for `&[u8]` by copying from the slice.
///
/// Note that reading updates the slice to point to the yet unread part.
/// The slice will be empty when EOF is reached.
impl<'a, E: Error> Read for Forward<&'a [u8], E> {
    type Error = E;
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, E> {
        let amt = cmp::min(buf.len(), self.0.len());
        let (a, b) = self.0.split_at(amt);
        buf[..amt].copy_from_slice(a);
        self.0 = b;
        Ok(amt)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), E> {
        if buf.len() > self.0.len() {
            return Err(E::unexpected_eof("failed to fill whole buffer"));
        }
        let (a, b) = self.0.split_at(buf.len());
        buf.copy_from_slice(a);
        self.0 = b;
        Ok(())
    }
}

impl<'a, E: Error> BufRead for Forward<&'a [u8], E> {
    #[inline]
    fn fill_buf(&mut self) -> Result<&[u8], E> { Ok(self.0) }

    #[inline]
    fn consume(&mut self, amt: usize) { self.0 = &self.0[amt..]; }
}

/// Write is implemented for `&mut [u8]` by copying into the slice, overwriting
/// its data.
///
/// Note that writing updates the slice to point to the yet unwritten part.
/// The slice will be empty when it has been completely overwritten.
impl<'a, E: Error> Write for Forward<&'a mut [u8], E> {
    type Error = E;
    #[inline]
    fn write(&mut self, data: &[u8]) -> Result<usize, E> {
        let amt = cmp::min(data.len(), self.0.len());
        let (a, b) = mem::replace(&mut self.0, &mut []).split_at_mut(amt);
        a.copy_from_slice(&data[..amt]);
        self.0 = b;
        Ok(amt)
    }

    #[inline]
    fn write_all(&mut self, data: &[u8]) -> Result<(), E> {
        if self.write(data)? == data.len() {
            Ok(())
        } else {
            Err(E::write_zero("failed to write whole buffer"))
        }
    }

    #[inline]
    fn flush(&mut self) -> Result<(), E> { Ok(()) }
}
