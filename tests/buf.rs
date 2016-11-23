extern crate io;

use io::prelude::*;
use io::{BufReader, BufWriter, LineWriter, SeekFrom, Error, Forward};

/// A dummy reader intended at testing short-reads propagation.
pub struct ShortReader {
    lengths: Vec<usize>,
}

impl Read for ShortReader {
    type Error = io::Void;
    fn read(&mut self, _: &mut [u8]) -> Result<usize, io::Void> {
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
    let buf = [0; 2];
    let mut reader = BufReader::new_preallocated(Forward::<_, io::Void>::new(inner), buf);

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
    let buf = [0; 2];
    let mut reader = BufReader::new_preallocated(io::Cursor::<_, io::Void>::new(inner), buf);

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
        type Error = io::Void;
        fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Void> {
            let len = buf.len();
            for x in buf {
                *x = self.pos as u8;
                self.pos = self.pos.wrapping_add(1);
            }
            Ok(len)
        }
    }
    impl Seek for PositionReader {
        type Error = io::Void;
        fn seek(&mut self, pos: SeekFrom) -> Result<u64, io::Void> {
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

    let mut reader = BufReader::new_preallocated(PositionReader { pos: 0 }, [0; 5]);
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
    let buf = (&mut [0u8; 99]) as &mut [u8];
    let inner = Forward::<_, io::Void>::new(buf);
    let mut writer = BufWriter::new_preallocated(inner, [0; 2]);

    writer.write(&[0, 1]).unwrap();
    assert_eq!(writer.get_ref().len(), 97);

    writer.write(&[2]).unwrap();
    assert_eq!(writer.get_ref().len(), 97);

    writer.write(&[3]).unwrap();
    assert_eq!(writer.get_ref().len(), 97);

    writer.flush().unwrap();
    assert_eq!(writer.get_ref().len(), 95);

    writer.write(&[4]).unwrap();
    writer.write(&[5]).unwrap();
    assert_eq!(writer.get_ref().len(), 95);

    writer.write(&[6]).unwrap();
    assert_eq!(writer.get_ref().len(), 93);

    writer.write(&[7, 8]).unwrap();
    assert_eq!(writer.get_ref().len(), 90);

    writer.write(&[9, 10, 11]).unwrap();
    assert_eq!(writer.get_ref().len(), 87);

    writer.flush().unwrap();
    assert_eq!(writer.get_ref().len(), 87);
}

#[test]
fn test_buffered_writer_inner_flushes() {
    let mut buf = [0u8; 99];
    let rest = {
        let inner = Forward::<_, io::Void>::new(&mut buf as &mut [u8]);
        let mut w = BufWriter::new_preallocated(inner, [0; 3]);
        w.write(&[0, 1]).unwrap();
        assert_eq!(w.get_ref().len(), 99);
        w.into_inner().unwrap().len()
    };
    assert_eq!(rest, 97);
    assert_eq!(buf[0..2], [0, 1]);
}

#[test]
fn test_buffered_writer_seek() {
    let inner: &mut [u8] = &mut [0; 99];
    let mut w = BufWriter::new_preallocated(io::Cursor::<_, io::Void>::new(inner), [0; 3]);
    w.write_all(&[0, 1, 2, 3, 4, 5]).unwrap();
    w.write_all(&[6, 7]).unwrap();
    assert_eq!(w.seek(SeekFrom::Current(0)).ok(), Some(8));
    assert_eq!(&w.get_ref().get_ref()[..8], &[0, 1, 2, 3, 4, 5, 6, 7][..]);
    assert_eq!(w.seek(SeekFrom::Start(2)).ok(), Some(2));
    w.write_all(&[8, 9]).unwrap();
    assert_eq!(&w.into_inner().unwrap().into_inner()[..8], &[0, 1, 8, 9, 4, 5, 6, 7]);
}

#[test]
fn test_line_buffer_fail_flush() {
    // Issue #32085
    struct FailFlushWriter<'a>(&'a mut Vec<u8>);

    struct FlushFailed;

    impl Error for FlushFailed {
        fn unexpected_eof(_: &'static str) -> Self { FlushFailed }
        fn is_interrupted(&self) -> bool { false }
        fn write_zero(_: &'static str) -> Self { FlushFailed }
        fn other(_: &'static str) -> Self { FlushFailed }
    }

    impl<'a> Write for FailFlushWriter<'a> {
        type Error = FlushFailed;
        fn write(&mut self, buf: &[u8]) -> Result<usize, FlushFailed> {
            self.0.extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> Result<(), FlushFailed> {
            Err(FlushFailed)
        }
    }

    let mut buf = Vec::new();
    {
        let mut writer = LineWriter::new_preallocated(FailFlushWriter(&mut buf), [0; 5]);
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
    let buf = (&mut [0u8; 99]) as &mut [u8];
    let buf = Forward::<_, io::Void>::new(buf);
    let mut writer = LineWriter::new_preallocated(buf, [0; 5]);
    writer.write(&[0]).unwrap();
    assert_eq!(writer.get_ref().len(), 99);
    writer.write(&[1]).unwrap();
    assert_eq!(writer.get_ref().len(), 99);
    writer.flush().unwrap();
    assert_eq!(writer.get_ref().len(), 97);
    writer.write(&[0, b'\n', 1, b'\n', 2]).unwrap();
    assert_eq!(writer.get_ref().len(), 93);
    writer.flush().unwrap();
    assert_eq!(writer.get_ref().len(), 92);
    writer.write(&[3, b'\n']).unwrap();
    assert_eq!(writer.get_ref().len(), 90);
}

#[test]
fn test_short_reads() {
    let inner = ShortReader{lengths: vec![0, 1, 2, 0, 1, 0]};
    let mut reader = BufReader::new_preallocated(inner, [0]);
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
    let reader = BufReader::new_preallocated(Forward::<_, io::Void>::new(&buf[..]), [0]);
    assert_eq!(reader.chars().next().unwrap().unwrap(), 'ß');
}

#[test]
fn test_chars() {
    let buf = [195, 159, b'a'];
    let reader = BufReader::new_preallocated(Forward::<_, io::Void>::new(&buf[..]), [0]);
    let mut it = reader.chars();
    assert_eq!(it.next().unwrap().unwrap(), 'ß');
    assert_eq!(it.next().unwrap().unwrap(), 'a');
    assert!(it.next().is_none());
}

#[test]
#[should_panic]
fn dont_panic_in_drop_on_panicked_flush() {
    struct FailFlushWriter;

    struct FailFlush;

    impl Error for FailFlush {
        fn unexpected_eof(_: &'static str) -> Self { FailFlush }
        fn is_interrupted(&self) -> bool { false }
        fn write_zero(_: &'static str) -> Self { FailFlush }
        fn other(_: &'static str) -> Self { FailFlush }
    }

    impl Write for FailFlushWriter {
        type Error = FailFlush;
        fn write(&mut self, buf: &[u8]) -> Result<usize, FailFlush> { Ok(buf.len()) }
        fn flush(&mut self) -> Result<(), FailFlush> {
            Err(FailFlush)
        }
    }

    let writer = FailFlushWriter;
    let _writer = BufWriter::new_preallocated(writer, []);

    // If writer panics *again* due to the flush error then the process will
    // abort.
    panic!();
}

#[test]
#[cfg_attr(target_os = "emscripten", ignore)]
#[cfg(feature = "std")]
fn panic_in_write_doesnt_flush_in_drop() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::thread;

    struct PanicWriter(Arc<AtomicUsize>);

    impl Write for PanicWriter {
        type Error = ::std::io::Error;
        fn write(&mut self, _: &[u8]) -> ::std::io::Result<usize> {
            self.0.fetch_add(1, Ordering::SeqCst);
            panic!();
        }
        fn flush(&mut self) -> ::std::io::Result<()> { Ok(()) }
    }

    let arc = Arc::new(AtomicUsize::new(0));
    let arc2 = arc.clone();
    thread::spawn(|| {
        let mut writer = BufWriter::new_preallocated(PanicWriter(arc2), [0; 2]);
        let _ = writer.write(b"hello world");
        let _ = writer.flush();
    }).join().unwrap_err();

    assert_eq!(arc.load(Ordering::SeqCst), 1);
}
