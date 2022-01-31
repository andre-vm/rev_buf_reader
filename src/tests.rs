use super::RevBufReader;
use std::io::prelude::*;
use std::io::{self, SeekFrom};

#[test]
fn test_buffered_reader() {
    let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
    let mut reader = RevBufReader::with_capacity(2, io::Cursor::new(inner));

    let mut buf = [0, 0, 0];
    let nread = reader.read(&mut buf);
    assert_eq!(nread.unwrap(), 3);
    assert_eq!(buf, [2, 3, 4]);
    assert_eq!(reader.buffer(), []);

    let mut buf = [0, 0];
    let nread = reader.read(&mut buf);
    assert_eq!(nread.unwrap(), 2);
    assert_eq!(buf, [0, 1]);
    assert_eq!(reader.buffer(), []);

    let mut buf = [0];
    let nread = reader.read(&mut buf);
    assert_eq!(nread.unwrap(), 1);
    assert_eq!(buf, [7]);
    assert_eq!(reader.buffer(), [6]);

    let mut buf = [0, 0, 0];
    let nread = reader.read(&mut buf);
    assert_eq!(nread.unwrap(), 1);
    assert_eq!(buf, [6, 0, 0]);
    assert_eq!(reader.buffer(), []);

    let nread = reader.read(&mut buf);
    assert_eq!(nread.unwrap(), 1);
    assert_eq!(buf, [5, 0, 0]);
    assert_eq!(reader.buffer(), []);

    assert_eq!(reader.read(&mut buf).unwrap(), 0);
}

#[test]
fn test_buffered_reader_seek() {
    let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
    let mut reader = RevBufReader::with_capacity(2, io::Cursor::new(inner));

    assert_eq!(reader.seek(SeekFrom::End(-3)).ok(), Some(5));
    assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
    assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(5));
    assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
    assert_eq!(reader.seek(SeekFrom::Current(-1)).ok(), Some(4));
    assert_eq!(reader.fill_buf().ok(), Some(&[7, 0][..]));
    reader.consume(1);
    assert_eq!(reader.seek(SeekFrom::Current(2)).ok(), Some(5));
}

#[test]
fn test_buffered_reader_seek_relative() {
    let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
    let mut reader = RevBufReader::with_capacity(2, io::Cursor::new(inner));

    assert!(reader.seek_relative(-3).is_ok());
    assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
    assert!(reader.seek_relative(0).is_ok());
    assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
    assert!(reader.seek_relative(-1).is_ok());
    assert_eq!(reader.fill_buf().ok(), Some(&[0][..]));
    assert!(reader.seek_relative(1).is_ok());
    assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
    assert!(reader.seek_relative(-2).is_ok());
    assert_eq!(reader.fill_buf().ok(), Some(&[6, 7][..]));
}

#[test]
fn test_buffered_reader_invalidated_after_read() {
    let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
    let mut reader = RevBufReader::with_capacity(3, io::Cursor::new(inner));

    assert_eq!(reader.fill_buf().ok(), Some(&[2, 3, 4][..]));
    reader.consume(3);

    let mut buffer = [0, 0, 0, 0, 0];
    assert_eq!(reader.read(&mut buffer).ok(), Some(5));
    assert_eq!(buffer, [5, 6, 7, 0, 1]);

    assert!(reader.seek_relative(2).is_ok());
    let mut buffer = [0, 0];
    assert_eq!(reader.read(&mut buffer).ok(), Some(2));
    assert_eq!(buffer, [5, 6]);
}

#[test]
fn test_buffered_reader_invalidated_after_seek() {
    let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
    let mut reader = RevBufReader::with_capacity(3, io::Cursor::new(inner));

    assert_eq!(reader.fill_buf().ok(), Some(&[2, 3, 4][..]));
    reader.consume(3);

    assert!(reader.seek(SeekFrom::Current(-5)).is_ok());

    assert!(reader.seek_relative(2).is_ok());
    let mut buffer = [0, 0];
    assert_eq!(reader.read(&mut buffer).ok(), Some(2));
    assert_eq!(buffer, [5, 6]);
}

#[test]
fn test_buffered_reader_seek_underflow() {
    // gimmick reader that yields its position modulo 256 for each byte
    struct PositionReader {
        pos: u64,
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
                    self.pos = n as u64;
                }
            }
            Ok(self.pos)
        }
    }

    let mut reader = RevBufReader::with_capacity(5, PositionReader { pos: 0 });
    assert_eq!(reader.fill_buf().ok(), Some(&[251, 252, 253, 254, 255][..]));
    assert_eq!(reader.seek(SeekFrom::Start(5)).ok(), Some(5));
    assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
    // the following seek will require two underlying seeks
    let expected = 9_223_372_036_854_775_813;
    assert_eq!(
        reader.seek(SeekFrom::Current(i64::min_value())).ok(),
        Some(expected)
    );
    assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
    // seeking to 0 should empty the buffer.
    assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(expected));
    assert_eq!(reader.get_ref().pos, expected);
}

#[test]
fn test_buffered_reader_seek_underflow_discard_buffer_between_seeks() {
    // gimmick reader that returns Err after a fixed number of seeks
    struct ErrAfterSomeSeeksReader {
        remaining_seeks: usize,
    }
    impl Read for ErrAfterSomeSeeksReader {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            for x in &mut *buf {
                *x = 0;
            }
            Ok(buf.len())
        }
    }
    impl Seek for ErrAfterSomeSeeksReader {
        fn seek(&mut self, _: SeekFrom) -> io::Result<u64> {
            if self.remaining_seeks > 0 {
                self.remaining_seeks -= 1;
                Ok(0)
            } else {
                Err(io::Error::new(io::ErrorKind::Other, "oh no!"))
            }
        }
    }

    // Just creating the RevBufReader requires a seek to the end of the stream.
    // Another seek is required to fill the buffer.
    let mut reader = RevBufReader::with_capacity(5, ErrAfterSomeSeeksReader { remaining_seeks: 3 });
    assert_eq!(reader.fill_buf().ok(), Some(&[0, 0, 0, 0, 0][..]));

    // Read one byte to place the RevBufReader cursor behind 0.
    let mut buf: [u8; 1] = [0];
    assert_eq!(reader.read(&mut buf).ok(), Some(1));

    // The following seek will require two underlying seeks.  The first will
    // succeed but the second will fail.  This should still invalidate the
    // buffer.
    assert!(reader.seek(SeekFrom::Current(i64::min_value())).is_err());
    assert_eq!(reader.buffer().len(), 0);
}

#[test]
fn test_read_until() {
    let inner: &[u8] = &[0, 1, 2, 1, 0];
    let mut reader = RevBufReader::with_capacity(2, io::Cursor::new(inner));
    let mut v = Vec::new();
    reader.read_until(1, &mut v).unwrap();
    assert_eq!(v, [0]);
    v.truncate(0);
    reader.read_until(1, &mut v).unwrap();
    assert_eq!(v, [2, 1]);
    v.truncate(0);
    reader.read_until(0, &mut v).unwrap();
    assert_eq!(v, [1]);
    v.truncate(0);
    reader.read_until(8, &mut v).unwrap();
    assert_eq!(v, [0]);
    v.truncate(0);
    reader.read_until(9, &mut v).unwrap();
    assert_eq!(v, []);
}

#[test]
fn test_read_line() {
    let in_buf: &[u8] = b"a\nb\nc";
    let mut reader = RevBufReader::with_capacity(2, io::Cursor::new(in_buf));
    let mut s = String::new();
    reader.read_line(&mut s).unwrap();
    assert_eq!(s, "c");
    s.truncate(0);
    reader.read_line(&mut s).unwrap();
    assert_eq!(s, "b\n");
    s.truncate(0);
    reader.read_line(&mut s).unwrap();
    assert_eq!(s, "a\n");
    s.truncate(0);
    reader.read_line(&mut s).unwrap();
    assert_eq!(s, "");
}

#[test]
fn test_lines() {
    let in_buf: &[u8] = b"a\nb\nc";
    let reader = RevBufReader::with_capacity(2, io::Cursor::new(in_buf));
    let mut it = reader.lines();
    assert_eq!(it.next().unwrap().unwrap(), "c".to_string());
    assert_eq!(it.next().unwrap().unwrap(), "b".to_string());
    assert_eq!(it.next().unwrap().unwrap(), "a".to_string());
    assert!(it.next().is_none());
}
