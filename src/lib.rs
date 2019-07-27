/*!
This crate provides a buffered reader capable of reading chunks of bytes of a
data stream in reverse order. Its implementation is an adapted copy of
[BufReader](https://doc.rust-lang.org/std/io/trait.BufRead.html) from the
nightly `std::io`.

# Usage

## Reading chunks of bytes in reverse order:

```rust
extern crate rev_buf_reader;

use rev_buf_reader::RevBufReader;
use std::io::{self, Read};

fn main() {
    let data = [0, 1, 2, 3, 4, 5, 6, 7];
    let inner = io::Cursor::new(&data);
    let mut reader = RevBufReader::new(inner);

    let mut buffer = [0, 0, 0];
    assert_eq!(reader.read(&mut buffer).ok(), Some(3));
    assert_eq!(buffer, [5, 6, 7]);

    let mut buffer = [0, 0, 0, 0, 0];
    assert_eq!(reader.read(&mut buffer).ok(), Some(5));
    assert_eq!(buffer, [0, 1, 2, 3, 4]);
}
```

## Reading text lines in reverse order:

```rust
extern crate rev_buf_reader;

use rev_buf_reader::RevBufReader;
use std::io::{self, BufRead};

fn main() {
    let data = "a\nb\nc";
    let inner = io::Cursor::new(&data);
    let reader = RevBufReader::new(inner);
    let mut lines = reader.lines();

    assert_eq!(lines.next().unwrap().unwrap(), "c".to_string());
    assert_eq!(lines.next().unwrap().unwrap(), "b".to_string());
    assert_eq!(lines.next().unwrap().unwrap(), "a".to_string());
    assert!(lines.next().is_none());
}
```
 */

#![cfg_attr(feature = "iovec", feature(iovec))]
#![cfg_attr(feature = "read_initializer", feature(read_initializer))]

extern crate memchr;

use std::io::prelude::*;

use std::fmt;
use std::io::{self, SeekFrom};

#[cfg(feature = "iovec")]
use std::io::IoSliceMut;

#[cfg(feature = "read_initializer")]
use std::io::Initializer;

use std::str;

const DEFAULT_BUF_SIZE: usize = 8 * 1024;

struct Guard<'a> {
    buf: &'a mut Vec<u8>,
    len: usize,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        unsafe {
            self.buf.set_len(self.len);
        }
    }
}

// The method `read_line` will append data into a `String` buffer, but we need to
// be pretty careful when doing this. The implementation will just call
// `.as_mut_vec()` and then delegate to a byte-oriented reading method, but we
// must ensure that when returning we never leave `buf` in a state such that it
// contains invalid UTF-8 in its bounds.
//
// To this end, we use an RAII guard (to protect against panics) which updates
// the length of the string when it is dropped. This guard initially truncates
// the string to the prior length and only after we've validated that the
// new contents are valid UTF-8 do we allow it to set a longer length.
//
// The unsafety in this function is twofold:
//
// 1. We're looking at the raw bytes of `buf`, so we take on the burden of UTF-8
//    checks.
// 2. We're passing a raw buffer to the function `f`, and it is expected that
//    the function only *appends* bytes to the buffer. We'll get undefined
//    behavior if existing bytes are overwritten to have non-UTF-8 data.
fn append_to_string<F>(buf: &mut String, f: F) -> io::Result<usize>
where
    F: FnOnce(&mut Vec<u8>) -> io::Result<usize>,
{
    unsafe {
        let mut g = Guard {
            len: buf.len(),
            buf: buf.as_mut_vec(),
        };
        let ret = f(g.buf);
        if str::from_utf8(&g.buf[g.len..]).is_err() {
            ret.and_then(|_| {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "stream did not contain valid UTF-8",
                ))
            })
        } else {
            g.len = g.buf.len();
            ret
        }
    }
}

fn read_until<R: BufRead + ?Sized>(r: &mut R, delim: u8, buf: &mut Vec<u8>) -> io::Result<usize> {
    let mut read = loop {
        let mut first = [0u8; 1];
        match r.read(&mut first) {
            Ok(n) => {
                buf.extend_from_slice(&first[..n]);
                break n;
            }
            Err(ref e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    };
    loop {
        let (done, used) = {
            let available = match r.fill_buf() {
                Ok(n) => n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            };
            match memchr::memrchr(delim, available) {
                Some(mut i) => {
                    i += 1; // Skip actual detected delimiter
                    buf.splice(..0, available[i..].iter().cloned());
                    (true, available.len() - i)
                }
                None => {
                    buf.splice(..0, available.iter().cloned());
                    (false, available.len())
                }
            }
        };
        r.consume(used);
        read += used;
        if done || used == 0 {
            return Ok(read);
        }
    }
}

/// `RevBufReader` is a struct similar to `std::io::BufReader`, which adds
/// buffering to any reader. But unlike `BufReader`, `RevBufReader` reads a
/// data stream from the end to the start. The order of the bytes, however,
/// remains the same. For example, when using `RevBufReader` to read a text file,
/// we can read the same lines as we would by using `BufReader`, but starting
/// from the last line until we get to the first one.
///
/// In order to able to read a data stream in reverse order, it must implement
/// both `std::io::Read` and `std::io::Seek`.
///
/// [`Read`]: ../../std/io/trait.Read.html
/// [`Seek`]: ../../std/io/trait.Seek.html
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
///     println!("Last line is {} bytes long", len);
///     Ok(())
/// }
/// ```
pub struct RevBufReader<R> {
    inner: R,
    buf: Box<[u8]>,
    pos: usize,
    cap: usize,
}

impl<R: Read + Seek> RevBufReader<R> {
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
    pub fn with_capacity(capacity: usize, mut inner: R) -> RevBufReader<R> {
        unsafe {
            let mut buffer = Vec::with_capacity(capacity);
            buffer.set_len(capacity);

            #[cfg(feature = "read_initializer")]
            inner.initializer().initialize(&mut buffer);

            inner
                .seek(SeekFrom::End(0))
                .expect("Cannot find the end of the stream.");
            RevBufReader {
                inner,
                buf: buffer.into_boxed_slice(),
                pos: 0,
                cap: 0,
            }
        }
    }

    /// Tries to seek `-length` bytes from the current position in the inner stream.
    /// It can fail because we may be trying to seek behind the start of the stream.
    /// If that's the case, we seek to the start of the stream, instead. It returns
    /// a result containing the absolute value of the actual offset that was sought.
    /// Other errors may occur during this operation, which will be passed to the caller.
    #[inline]
    fn checked_seek_back(&mut self, length: usize) -> io::Result<usize> {
        // It should be safe to assume that offset fits within an i64 as the alternative
        // means we managed to allocate 8 exbibytes and that's absurd.
        let offset = (self.cap + length) as i64;
        // This can fail if we're trying to seek to a negative offset.
        let checked_length = match self.inner.seek(SeekFrom::Current(-offset)) {
            Ok(_) => length,
            Err(error) => {
                let position = self.inner.seek(SeekFrom::Current(0))? as usize;
                if position > offset as usize {
                    // In this case, the error is not due to seeking to a negative offset.
                    return Err(error);
                }
                self.inner.seek(SeekFrom::Start(0))?;
                position.saturating_sub(self.cap)
            }
        };
        self.cap = 0;
        Ok(checked_length)
    }
}

impl<R> RevBufReader<R> {
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
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

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
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Returns a reference to the internally buffered data.
    ///
    /// Unlike `fill_buf`, this will not attempt to fill the buffer if it is empty.
    ///
    /// # Examples
    ///
    /// ```no_run
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
        &self.buf[0..self.pos]
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
    pub fn into_inner(self) -> R {
        self.inner
    }
    
    /// Invalidates all data in the internal buffer.
    #[inline]
    fn discard_buffer(&mut self) {
        self.pos = 0;
        self.cap = 0;
    }
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
                return Ok(());
            }
        } else {
            if let Some(new_pos) = pos.checked_add(offset as u64) {
                if new_pos <= self.cap as u64 {
                    self.pos = new_pos as usize;
                    return Ok(());
                }
            }
        }
        self.seek(SeekFrom::Current(offset)).map(|_| ())
    }
}

impl<R: Read + Seek> Read for RevBufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if self.pos == 0 && buf.len() >= self.buf.len() {
            let length = self.checked_seek_back(buf.len())?;
            self.inner
                .read_exact(&mut buf[..length])
                .expect("Should be able to read the checked amount of data.");
            self.inner
                .seek(SeekFrom::Current(-(length as i64)))
                .expect("Unable to seek back to previous position.");
            return Ok(length);
        }
        let nread = {
            let rem = self.fill_buf()?;
            let offset = rem.len().saturating_sub(buf.len());
            let mut rem = &rem[offset..];
            rem.read(buf)?
        };
        self.consume(nread);
        Ok(nread)
    }

    #[cfg(feature = "iovec")]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum::<usize>();
        if self.pos == self.cap && total_len >= self.buf.len() {
            let length = self.checked_seek_back(total_len)?;
            self.inner
                .read_vectored(bufs)
                .expect("Should be able to read the checked amount of data.");
            self.inner
                .seek(SeekFrom::Current(-(length as i64)))
                .expect("Unable to seek back to previous position.");
            return Ok(length);
        }
        let nread = {
            let rem = self.fill_buf()?;
            let offset = rem.len().saturating_sub(total_len);
            let mut rem = &rem[offset..];
            rem.read_vectored(bufs)?
        };
        self.consume(nread);
        Ok(nread)
    }

    // We can't skip unconditionally because of the large buffer case in read.
    #[cfg(feature = "read_initializer")]
    unsafe fn initializer(&self) -> Initializer {
        self.inner.initializer()
    }
}

impl<R: Read + Seek> BufRead for RevBufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        if self.pos == 0 {
            let length = self.checked_seek_back(self.buf.len())?;
            self.inner
                .read_exact(&mut self.buf[..length])
                .expect("Should be able to read the checked amount of data.");
            self.cap = length;
            self.pos = self.cap;
        }
        Ok(&self.buf[0..self.pos])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = self.pos.saturating_sub(amt);
    }

    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> io::Result<usize> {
        read_until(self, byte, buf)
    }

    fn read_line(&mut self, buf: &mut String) -> io::Result<usize> {
        // Note that we are not calling the `.read_until` method here, but
        // rather our hardcoded implementation. For more details as to why, see
        // the comments in `read_to_end`.
        append_to_string(buf, |b| read_until(self, b'\n', b))
    }
}

impl<R> fmt::Debug for RevBufReader<R>
where
    R: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("RevBufReader")
            .field("reader", &self.inner)
            .field("buffer", &format_args!("{}/{}", self.pos, self.buf.len()))
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
            // It should be safe to assume that remainder fits within an i64 as the alternative
            // means we managed to allocate 8 exbibytes and that's absurd.
            // But it's not out of the realm of possibility for some weird underlying reader to
            // support seeking by i64::min_value() so we need to handle underflow when subtracting
            // remainder.
            if let Some(offset) = n.checked_sub(remainder) {
                result = self.inner.seek(SeekFrom::Current(offset))?;
            } else {
                // Seek backwards by our remainder, and then by the offset
                self.inner.seek(SeekFrom::Current(-remainder))?;
                self.discard_buffer();
                result = self.inner.seek(SeekFrom::Current(n))?;
            }
        } else {
            // Seeking with Start/End doesn't care about our buffer length.
            result = self.inner.seek(pos)?;
        }
        self.discard_buffer();
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
}
