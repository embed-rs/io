use ::{Read, Write, Seek, BufRead, SeekFrom, Error};

impl<R: ::std::io::Read> Read for R {
    type Error = ::std::io::Error;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        ::std::io::Read::read(self, buf)
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
        ::std::io::Read::read_exact(self, buf)
    }
}

impl<W: ::std::io::Write> Write for W {
    type Error = ::std::io::Error;
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        ::std::io::Write::write(self, buf)
    }
    fn write_all(&mut self, buf: &[u8]) -> Result<(), Self::Error> {
        ::std::io::Write::write_all(self, buf)
    }
    fn write_fmt(&mut self, args: ::core::fmt::Arguments) -> Result<(), Self::Error> {
        ::std::io::Write::write_fmt(self, args)
    }
    fn flush(&mut self) -> Result<(), Self::Error> {
        ::std::io::Write::flush(self)
    }
}

impl<S: ::std::io::Seek> Seek for S {
    type Error = ::std::io::Error;
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let pos = match pos {
            SeekFrom::Start(n) => ::std::io::SeekFrom::Start(n),
            SeekFrom::End(n) => ::std::io::SeekFrom::End(n),
            SeekFrom::Current(n) => ::std::io::SeekFrom::Current(n),
        };
        ::std::io::Seek::seek(self, pos)
    }
}

impl<B: ::std::io::BufRead> BufRead for B {
    fn fill_buf(&mut self) -> Result<&[u8], <Self as Read>::Error> {
        ::std::io::BufRead::fill_buf(self)
    }
    fn consume(&mut self, amt: usize) {
        ::std::io::BufRead::consume(self, amt)
    }
}

impl Error for ::std::io::Error {
    fn unexpected_eof(s: &'static str) -> Self {
        ::std::io::Error::new(::std::io::ErrorKind::UnexpectedEof, s)
    }
    fn is_interrupted(&self) -> bool {
        self.kind() == ::std::io::ErrorKind::Interrupted
    }
    fn write_zero(s: &'static str) -> Self {
        ::std::io::Error::new(::std::io::ErrorKind::WriteZero, s)
    }
    fn other(s: &'static str) -> Self {
        ::std::io::Error::new(::std::io::ErrorKind::Other, s)
    }
}
