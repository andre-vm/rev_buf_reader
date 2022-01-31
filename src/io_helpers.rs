extern crate memchr;

use std::io;
use std::io::prelude::*;

use std::str;

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
pub(crate) unsafe fn append_to_string<F>(buf: &mut String, f: F) -> io::Result<usize>
where
    F: FnOnce(&mut Vec<u8>) -> io::Result<usize>,
{
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

pub(crate) fn read_until<R: BufRead + ?Sized>(
    r: &mut R,
    delim: u8,
    buf: &mut Vec<u8>,
) -> io::Result<usize> {
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
