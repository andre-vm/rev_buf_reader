This folder contains a copy of some files from the libstd folder belonging to the master branch of the Rust repository. The implementation of RevBufReader is based on those files, so every time a new change is made to one of them in the Rust repository it is recommended to update the RevBufReader implementation according to those changes:

1. Check the diffs between the files from the Rust repository and the ones in the base folder
1. Update the implementation of RevBufReader taking those diffs into account
1. Replace the file in the base folder with the new version from the Rust repository