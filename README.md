# lis

Rust implementation of the
[Longest increasing subsequence algorithm](https://en.wikipedia.org/wiki/Longest_increasing_subsequence).

[![Build Status](https://travis-ci.org/axelf4/lis.svg?branch=master)](https://travis-ci.org/axelf4/lis)
[![Documentation](https://docs.rs/lis/badge.svg)](https://docs.rs/lis)

Also provides a function for diffing lists, that makes use of the LIS algorithm.
Requires the unstable feature `generators` and thus the nightly compiler.

# Examples

The main trait exposed by this crate is `LisExt`, which is implemented for,
inter alia, arrays:

```rust
use lis::LisExt;
assert_eq!([2, 1, 4, 3, 5].longest_increasing_subsequence(), [1, 3, 4]);
```

Diffing two lists can be done with `diff_by_key`:

```rust
#![feature(generator_trait)]
use lis::{diff_by_key, DiffAction};
use std::ops::{Generator, GeneratorState};
let mut generator = diff_by_key(1..2, 1..3, |x| x);
assert_eq!(unsafe { generator.resume() }, GeneratorState::Yielded(DiffAction::Unchanged(1, 1)));
assert_eq!(unsafe { generator.resume() }, GeneratorState::Yielded(DiffAction::Insert(2)));
assert_eq!(unsafe { generator.resume() }, GeneratorState::Complete(()));
```
