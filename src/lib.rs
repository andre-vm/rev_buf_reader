#![feature(read_initializer)]

use std::io::prelude::*;

use std::cmp;
use std::fmt;
use std::io::{self, Initializer, SeekFrom};

const DEFAULT_BUF_SIZE: usize = 8 * 1024;

/// The `RevBufReader` struct adds buffering to any reader.
///
/// It can be excessively inefficient to work directly with a [`Read`] instance.
/// For example, every call to [`read`][`TcpStream::read`] on [`TcpStream`]
/// results in a system call. A `RevBufReader` performs large, infrequent reads on
/// the underlying [`Read`] and maintains an in-memory buffer of the results.
///
/// `RevBufReader` can improve the speed of programs that make *small* and
/// *repeated* read calls to the same file or network socket. It does not
/// help when reading very large amounts at once, or reading just one or a few
/// times. It also provides no advantage when reading from a source that is
/// already in memory, like a `Vec<u8>`.
///
/// [`Read`]: ../../std/io/trait.Read.html
/// [`TcpStream::read`]: ../../std/net/struct.TcpStream.html#method.read
/// [`TcpStream`]: ../../std/net/struct.TcpStream.html
///
/// # Examples
///
/// ```no_run
/// use rev_buf_reader::RevBufReader;
/// use std::io::prelude::*;
/// use std::fs::File;
///
/// fn main() -> std::io::Result<()> {
///     let f = File::open("log.txt")?;
///     let mut reader = RevBufReader::new(f);
///
///     let mut line = String::new();
///     let len = reader.read_line(&mut line)?;
///     println!("First line is {} bytes long", len);
///     Ok(())
/// }
/// ```
pub struct RevBufReader<R> {
    inner: R,
    buf: Box<[u8]>,
    pos: usize,
    cap: usize,
}

impl<R: Read> RevBufReader<R> {
    /// Creates a new `RevBufReader` with a default buffer capacity. The default is currently 8 KB,
    /// but may change in the future.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use rev_buf_reader::RevBufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let reader = RevBufReader::new(f);
    ///     Ok(())
    /// }
    /// ```
    pub fn new(inner: R) -> RevBufReader<R> {
        RevBufReader::with_capacity(DEFAULT_BUF_SIZE, inner)
    }

    /// Creates a new `RevBufReader` with the specified buffer capacity.
    ///
    /// # Examples
    ///
    /// Creating a buffer with ten bytes of capacity:
    ///
    /// ```no_run
    /// use rev_buf_reader::RevBufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let reader = RevBufReader::with_capacity(10, f);
    ///     Ok(())
    /// }
    /// ```
    pub fn with_capacity(cap: usize, inner: R) -> RevBufReader<R> {
        unsafe {
            let mut buffer = Vec::with_capacity(cap);
            buffer.set_len(cap);
            inner.initializer().initialize(&mut buffer);
            RevBufReader {
                inner,
                buf: buffer.into_boxed_slice(),
                pos: 0,
                cap: 0,
            }
        }
    }

    /// Gets a reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use rev_buf_reader::RevBufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f1 = File::open("log.txt")?;
    ///     let reader = RevBufReader::new(f1);
    ///
    ///     let f2 = reader.get_ref();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_ref(&self) -> &R { &self.inner }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use rev_buf_reader::RevBufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f1 = File::open("log.txt")?;
    ///     let mut reader = RevBufReader::new(f1);
    ///
    ///     let f2 = reader.get_mut();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut R { &mut self.inner }

    /// Returns a reference to the internally buffered data.
    ///
    /// Unlike `fill_buf`, this will not attempt to fill the buffer if it is empty.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #![feature(bufreader_buffer)]
    /// use rev_buf_reader::RevBufReader;
    /// use std::io::BufRead;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let mut reader = RevBufReader::new(f);
    ///     assert!(reader.buffer().is_empty());
    ///
    ///     if reader.fill_buf()?.len() > 0 {
    ///         assert!(!reader.buffer().is_empty());
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub fn buffer(&self) -> &[u8] {
        &self.buf[self.pos..self.cap]
    }

    /// Unwraps this `RevBufReader`, returning the underlying reader.
    ///
    /// Note that any leftover data in the internal buffer is lost.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use rev_buf_reader::RevBufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f1 = File::open("log.txt")?;
    ///     let reader = RevBufReader::new(f1);
    ///
    ///     let f2 = reader.into_inner();
    ///     Ok(())
    /// }
    /// ```
    pub fn into_inner(self) -> R { self.inner }
}

impl<R: Seek> RevBufReader<R> {
    /// Seeks relative to the current position. If the new position lies within the buffer,
    /// the buffer will not be flushed, allowing for more efficient seeks.
    /// This method does not return the location of the underlying reader, so the caller
    /// must track this information themselves if it is required.
    pub fn seek_relative(&mut self, offset: i64) -> io::Result<()> {
        let pos = self.pos as u64;
        if offset < 0 {
            if let Some(new_pos) = pos.checked_sub((-offset) as u64) {
                self.pos = new_pos as usize;
                return Ok(())
            }
        } else {
            if let Some(new_pos) = pos.checked_add(offset as u64) {
                if new_pos <= self.cap as u64 {
                    self.pos = new_pos as usize;
                    return Ok(())
                }
            }
        }
        self.seek(SeekFrom::Current(offset)).map(|_|())
    }
}

impl<R: Read> Read for RevBufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if self.pos == self.cap && buf.len() >= self.buf.len() {
            return self.inner.read(buf);
        }
        let nread = {
            let mut rem = self.fill_buf()?;
            rem.read(buf)?
        };
        self.consume(nread);
        Ok(nread)
    }

    // we can't skip unconditionally because of the large buffer case in read.
    unsafe fn initializer(&self) -> Initializer {
        self.inner.initializer()
    }
}

impl<R: Read> BufRead for RevBufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.
        if self.pos >= self.cap {
            debug_assert!(self.pos == self.cap);
            self.cap = self.inner.read(&mut self.buf)?;
            self.pos = 0;
        }
        Ok(&self.buf[self.pos..self.cap])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = cmp::min(self.pos + amt, self.cap);
    }
}

impl<R> fmt::Debug for RevBufReader<R> where R: fmt::Debug {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("RevBufReader")
            .field("reader", &self.inner)
            .field("buffer", &format_args!("{}/{}", self.cap - self.pos, self.buf.len()))
            .finish()
    }
}

impl<R: Seek> Seek for RevBufReader<R> {
    /// Seek to an offset, in bytes, in the underlying reader.
    ///
    /// The position used for seeking with `SeekFrom::Current(_)` is the
    /// position the underlying reader would be at if the `RevBufReader` had no
    /// internal buffer.
    ///
    /// Seeking always discards the internal buffer, even if the seek position
    /// would otherwise fall within it. This guarantees that calling
    /// `.into_inner()` immediately after a seek yields the underlying reader
    /// at the same position.
    ///
    /// To seek without discarding the internal buffer, use [`RevBufReader::seek_relative`].
    ///
    /// See [`std::io::Seek`] for more details.
    ///
    /// Note: In the edge case where you're seeking with `SeekFrom::Current(n)`
    /// where `n` minus the internal buffer length overflows an `i64`, two
    /// seeks will be performed instead of one. If the second seek returns
    /// `Err`, the underlying reader will be left at the same position it would
    /// have if you called `seek` with `SeekFrom::Current(0)`.
    ///
    /// [`RevBufReader::seek_relative`]: struct.RevBufReader.html#method.seek_relative
    /// [`std::io::Seek`]: trait.Seek.html
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
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

#[cfg(test)]
mod tests {
    use super::RevBufReader;
    use std::io::prelude::*;
    use std::io::{self, SeekFrom};

    #[test]
    fn test_buffered_reader() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = RevBufReader::with_capacity(2, inner);

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

        let mut reader = RevBufReader::with_capacity(5, PositionReader { pos: 0 });
        assert_eq!(reader.fill_buf().ok(), Some(&[251, 252, 253, 254, 255][..]));
        assert_eq!(reader.seek(SeekFrom::Start(5)).ok(), Some(5));
        assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
        // the following seek will require two underlying seeks
        let expected = 9_223_372_036_854_775_813;
        assert_eq!(reader.seek(SeekFrom::Current(i64::min_value())).ok(), Some(expected));
        assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
        // seeking to 0 should empty the buffer.
        assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(expected));
        assert_eq!(reader.get_ref().pos, expected);
    }

    #[test]
    fn test_read_until() {
        let inner: &[u8] = &[0, 1, 2, 1, 0];
        let mut reader = RevBufReader::with_capacity(2, inner);
        let mut v = Vec::new();
        reader.read_until(0, &mut v).unwrap();
        assert_eq!(v, [0]);
        v.truncate(0);
        reader.read_until(2, &mut v).unwrap();
        assert_eq!(v, [2, 1]);
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
    fn test_read_line() {
        let in_buf: &[u8] = b"a\nb\nc";
        let mut reader = RevBufReader::with_capacity(2, in_buf);
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
        let reader = RevBufReader::with_capacity(2, in_buf);
        let mut it = reader.lines();
        assert_eq!(it.next().unwrap().unwrap(), "c".to_string());
        assert_eq!(it.next().unwrap().unwrap(), "b".to_string());
        assert_eq!(it.next().unwrap().unwrap(), "a".to_string());
        assert!(it.next().is_none());
    }

    #[test]
    fn test_short_reads() {
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

        let inner = ShortReader { lengths: vec![0, 1, 2, 0, 1, 0] };
        let mut reader = RevBufReader::new(inner);
        let mut buf = [0, 0];
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 1);
        assert_eq!(reader.read(&mut buf).unwrap(), 2);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 1);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
    }
}
