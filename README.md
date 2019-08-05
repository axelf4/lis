<img src="logo.svg" alt="Logo" align="right" width="175">

# lis

Rust implementation of the
[Longest increasing subsequence algorithm](https://en.wikipedia.org/wiki/Longest_increasing_subsequence).

[![Build Status](https://travis-ci.org/axelf4/lis.svg?branch=master)](https://travis-ci.org/axelf4/lis)
[![Documentation](https://docs.rs/lis/badge.svg)](https://docs.rs/lis)

Also provides a function for diffing lists, that makes use of the LIS algorithm.

# Examples

The main trait exposed by this crate is `LisExt`, which is implemented for,
inter alia, arrays:

```rust
use lis::LisExt;
assert_eq!([2, 1, 4, 3, 5].longest_increasing_subsequence(), [1, 3, 4]);
```

Diffing two lists can be done with `diff_by_key`:

```rust
use lis::{diff_by_key, DiffCallback};
struct Cb;
impl DiffCallback<usize, usize> for Cb {
    fn inserted(&mut self, new: usize) {
        assert_eq!(new, 2);
    }
    fn removed(&mut self, old: usize) {}
    fn unchanged(&mut self, old: usize, new: usize) {
        assert_eq!(old, 1);
        assert_eq!(new, 1);
    }
}
diff_by_key(1..2, |x| x, 1..3, |x| x, &mut Cb);
```
