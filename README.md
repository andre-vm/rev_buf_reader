# Description

RevBufReader is a BufReader capable of reading from the end towards the start. Its implementation is an adapted copy of the original BufReader from std::io.

# Update

The base folder contains a copy of the libstd/io/buffered.rs file from the Rust repository. The RevBufReader implementation is based on that file. Every time a new change is made to that file in the Rust repository, the following procedure must be done:

- Check the diffs between the buffered.rs file from the Rust repository and the one in the base folder
- Update the implementation of RevBufReader taking those diffs into account
- Replace the buffered.rs file in the base folder with the new version from the Rust repository