# Description

RevBufReader is a BufReader capable of reading from the end to the start. Its implementation is an adapted copy of the original BufReader from std::io.

# Update

The base folder contains a copy of the following files from libstd folder in the Rust repository:

- /io/buffered.rs
- /io/mod.rs
- /sys_common/io.rs

The RevBufReader implementation is based on those files. Every time a new change is made to one of them in the Rust repository, the following procedure must be done:

- Check the diffs between the files from the Rust repository and the ones in the base folder
- Update the implementation of RevBufReader taking those diffs into account
- Replace the file in the base folder with the new version from the Rust repository