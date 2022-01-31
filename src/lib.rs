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

let data = [0, 1, 2, 3, 4, 5, 6, 7];
let inner = io::Cursor::new(&data);
let mut reader = RevBufReader::new(inner);

let mut buffer = [0, 0, 0];
assert_eq!(reader.read(&mut buffer).ok(), Some(3));
assert_eq!(buffer, [5, 6, 7]);

let mut buffer = [0, 0, 0, 0, 0];
assert_eq!(reader.read(&mut buffer).ok(), Some(5));
assert_eq!(buffer, [0, 1, 2, 3, 4]);
```

## Reading text lines in reverse order:

```rust
extern crate rev_buf_reader;

use rev_buf_reader::RevBufReader;
use std::io::{self, BufRead};

let data = "a\nb\nc";
let inner = io::Cursor::new(&data);
let reader = RevBufReader::new(inner);
let mut lines = reader.lines();

assert_eq!(lines.next().unwrap().unwrap(), "c".to_string());
assert_eq!(lines.next().unwrap().unwrap(), "b".to_string());
assert_eq!(lines.next().unwrap().unwrap(), "a".to_string());
assert!(lines.next().is_none());
```
 */

#![cfg_attr(feature = "read_initializer", feature(read_initializer))]

use io_helpers::{append_to_string, read_until};

use std::io::prelude::*;

use std::fmt;
use std::io::{self, IoSliceMut, SeekFrom};

#[cfg(feature = "read_initializer")]
use std::io::Initializer;

mod io_helpers;

#[cfg(test)]
mod tests;

// Bare metal platforms usually have very small amounts of RAM
// (in the order of hundreds of KB)
const DEFAULT_BUF_SIZE: usize = if cfg!(target_os = "espidf") {
    512
} else {
    8 * 1024
};

/// `RevBufReader<R>` is a struct similar to `std::io::BufReader<R>`, which adds
/// buffering to any reader. But unlike `BufReader<R>`, `RevBufReader<R>` reads a
/// data stream from the end to the start. The order of the bytes, however,
/// remains the same. For example, when using `RevBufReader<R>` to read a text file,
/// we can read the same lines as we would by using `BufReader<R>`, but starting
/// from the last line until we get to the first one.
///
/// In order to able to read a data stream in reverse order, it must implement
/// both `std::io::Read` and `std::io::Seek`.
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
    /// Creates a new `RevBufReader<R>` with a default buffer capacity. The default is currently 8 KB,
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

    /// Creates a new `RevBufReader<R>` with the specified buffer capacity.
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
    /// Unlike [`fill_buf`], this will not attempt to fill the buffer if it is empty.
    ///
    /// [`fill_buf`]: BufRead::fill_buf
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

    /// Returns the number of bytes the internal buffer can hold at once.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use rev_buf_reader::RevBufReader;
    ///
    /// use std::io::{BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let mut reader = RevBufReader::new(f);
    ///
    ///     let capacity = reader.capacity();
    ///     let buffer = reader.fill_buf()?;
    ///     assert!(buffer.len() <= capacity);
    ///     Ok(())
    /// }
    /// ```
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Unwraps this `RevBufReader<R>`, returning the underlying reader.
    ///
    /// Note that any leftover data in the internal buffer is lost. Therefore,
    /// a following read from the underlying reader may lead to data loss.
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
        } else if let Some(new_pos) = pos.checked_add(offset as u64) {
            if new_pos <= self.cap as u64 {
                self.pos = new_pos as usize;
                return Ok(());
            }
        }

        self.seek(SeekFrom::Current(offset)).map(drop)
    }
}

impl<R: Read + Seek> Read for RevBufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if self.pos == 0 && buf.len() >= self.buf.len() {
            let length = self.checked_seek_back(buf.len())?;
            // This shouldn't error, as we just checked the amount of data.
            // However, it could error if `inner` can suddenly no longer read.
            self.inner.read_exact(&mut buf[..length])?;
            self.inner.seek(SeekFrom::Current(-(length as i64)))?;
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

    #[allow(clippy::unused_io_amount)]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum::<usize>();
        if self.pos == self.cap && total_len >= self.buf.len() {
            let length = self.checked_seek_back(total_len)?;
            // This shouldn't error, as we just checked the amount of data.
            // However, it could error if `inner` can suddenly no longer read.
            self.inner.read_vectored(bufs)?;
            self.inner.seek(SeekFrom::Current(-(length as i64)))?;
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
            self.inner.read_exact(&mut self.buf[..length])?;
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
        unsafe { append_to_string(buf, |b| read_until(self, b'\n', b)) }
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
    /// position the underlying reader would be at if the `RevBufReader<R>` had no
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
