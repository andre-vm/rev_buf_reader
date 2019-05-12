**rev_buf_reader** is Rust crate that provides a buffered reader capable of reading chunks of bytes of a data stream in reverse order. Its implementation is an adapted copy of BufReader from the nightly std::io.

[![](https://meritbadge.herokuapp.com/rev_buf_reader)](https://crates.io/crates/rev_buf_reader)

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

# Features

**rev_buf_reader** has two features that correspond to experimental features of nightly Rust:

- iovec 
- read_initializer

If you use these in your project by adding `#![feature(feature_name)]`, you'll need to enable these features for **rev_buf_reader** as well in your Cargo.toml.