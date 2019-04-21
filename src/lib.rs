/*!
An implementation of the
[Longest increasing subsequence algorithm](https://en.wikipedia.org/wiki/Longest_increasing_subsequence).

# Examples

The main trait exposed by this crate is [LisExt], which is implemented for,
inter alia, arrays:

```
use lis::LisExt;
assert_eq!([2, 1, 4, 3, 5].longest_increasing_subsequence(), [1, 3, 4]);
```

Diffing two lists can be done with [diff_by_key]:

```
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
*/

#![deny(missing_docs)]

use fxhash::FxHashMap;
use std::cmp::Ordering::{self, Greater, Less};
use std::hash::Hash;

/// Extends `AsRef<[T]>` with methods for generating longest increasing subsequences.
pub trait LisExt<T>: AsRef<[T]> {
    /// Returns indices of the longest increasing subsequence.
    ///
    /// See [`longest_increasing_subsequence_by`].
    ///
    /// [`longest_increasing_subsequence_by`]: #method.longest_increasing_subsequence_by
    #[inline]
    fn longest_increasing_subsequence(&self) -> Vec<usize>
    where
        T: Ord,
    {
        self.longest_increasing_subsequence_by(|a, b| a.cmp(b), |_| true)
    }

    /// Returns indices of the longest increasing subsequence with a comparator function.
    ///
    /// The closure `filter` is called on each element. If it returns `false` the element is
    /// skipped, however indices are left intact.
    ///
    /// This is `O(n log n)` worst-case and allocates at most `2 * 4 * n` bytes.
    /// It is based on the method described by Michael L. Fredman (1975) in [*On computing the
    /// length of longest increasing subsequences*](https://doi.org/10.1016/0012-365X(75)90103-X).
    ///
    /// # Example
    ///
    /// ```
    /// use lis::LisExt;
    /// assert_eq!([2, 1, 4, 3, 5].longest_increasing_subsequence_by(|a, b| a.cmp(b), |_| true), [1, 3, 4]);
    /// ```
    fn longest_increasing_subsequence_by<F, P>(&self, mut f: F, mut filter: P) -> Vec<usize>
    where
        F: FnMut(&T, &T) -> Ordering,
        P: FnMut(&T) -> bool,
    {
        let a = self.as_ref();
        let (mut p, mut m) = (vec![0; a.len()], Vec::with_capacity(a.len()));
        let mut it = a.iter().enumerate().filter(|(_, x)| filter(x));
        m.push(if let Some((i, _)) = it.next() {
            i
        } else {
            return Vec::new(); // The array was empty
        });

        for (i, x) in it {
            // Test whether a[i] can extend the current sequence
            if f(&a[*m.last().unwrap()], x) == Less {
                p[i] = *m.last().unwrap();
                m.push(i);
                continue;
            }

            // Binary search for largest j ≤ m.len() such that a[m[j]] < a[i]
            let j = match m.binary_search_by(|&j| f(&a[j], x).then(Greater)) {
                Ok(j) | Err(j) => j,
            };
            if j > 0 {
                p[i] = m[j - 1];
            }
            m[j] = i;
        }

        // Reconstruct the longest increasing subsequence
        let mut k = *m.last().unwrap();
        for i in (0..m.len()).rev() {
            m[i] = k;
            k = p[k];
        }
        m
    }
}

impl<S, T> LisExt<T> for S where S: AsRef<[T]> + ?Sized {}

/// Extends `Iterator` with an adapter that is peekable from both ends.
trait IteratorExt: Iterator {
    fn de_peekable(self) -> DoubleEndedPeekable<Self>
    where
        Self: Sized + DoubleEndedIterator,
    {
        DoubleEndedPeekable {
            iter: self,
            front: None,
            back: None,
        }
    }
}

impl<T: Iterator> IteratorExt for T {}

/// A double ended iterator that is peekable.
#[derive(Clone, Debug)]
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
struct DoubleEndedPeekable<I: Iterator> {
    iter: I,
    front: Option<Option<I::Item>>,
    back: Option<Option<I::Item>>,
}

impl<I: Iterator> DoubleEndedPeekable<I> {
    #[inline]
    fn peek(&mut self) -> Option<&I::Item> {
        if self.front.is_none() {
            self.front = Some(
                self.iter
                    .next()
                    .or_else(|| self.back.take().unwrap_or(None)),
            );
        }
        match self.front {
            Some(Some(ref value)) => Some(value),
            Some(None) => None,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn peek_back(&mut self) -> Option<&I::Item>
    where
        I: DoubleEndedIterator,
    {
        if self.back.is_none() {
            self.back = Some(
                self.iter
                    .next_back()
                    .or_else(|| self.front.take().unwrap_or(None)),
            );
        }
        match self.back {
            Some(Some(ref value)) => Some(value),
            Some(None) => None,
            _ => unreachable!(),
        }
    }
}

impl<I: Iterator> Iterator for DoubleEndedPeekable<I> {
    type Item = I::Item;
    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        self.front
            .take()
            .unwrap_or_else(|| self.iter.next())
            .or_else(|| self.back.take().unwrap_or(None))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let peek_len = match self.front {
            Some(None) => return (0, Some(0)),
            Some(Some(_)) => 1,
            None => 0,
        } + match self.back {
            Some(None) => return (0, Some(0)),
            Some(Some(_)) => 1,
            None => 0,
        };
        let (lo, hi) = self.iter.size_hint();
        (
            lo.saturating_add(peek_len),
            hi.and_then(|x| x.checked_add(peek_len)),
        )
    }
}

impl<I: DoubleEndedIterator> DoubleEndedIterator for DoubleEndedPeekable<I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back
            .take()
            .unwrap_or_else(|| self.iter.next_back())
            .or_else(|| self.front.take().unwrap_or(None))
    }
}

impl<I: std::iter::ExactSizeIterator> std::iter::ExactSizeIterator for DoubleEndedPeekable<I> {}
impl<I: std::iter::FusedIterator> std::iter::FusedIterator for DoubleEndedPeekable<I> {}

/// Gets notified for each step of the diffing process.
pub trait DiffCallback<S, T> {
    /// Called when a new element was inserted.
    fn inserted(&mut self, new: T);
    /// Called when an element stayed in place.
    fn unchanged(&mut self, old: S, new: T);
    /// Called when an element was removed.
    fn removed(&mut self, old: S);
    /// Called when an element was moved.
    fn moved(&mut self, old: S, new: T) {
        self.removed(old);
        self.inserted(new);
    }
}

/// Computes the difference between the two iterators with key extraction functions.
///
/// Keys have to be unique. Returns removals in forward order and insertions/moves in reverse order.
/// Guaranteed not to allocate if the changeset is entirely contiguous insertions or removals.
/// Result stores `S`/`T`:s instead of indices; use [enumerate] if preferable.
///
/// # Panics
///
/// May panic if `a` contains duplicate keys.
///
/// [enumerate]: std::iter::Iterator::enumerate
pub fn diff_by_key<S, T, K: Eq + Hash>(
    a: impl IntoIterator<Item = S, IntoIter = impl DoubleEndedIterator<Item = S>>,
    mut f: impl FnMut(&S) -> &K,
    b: impl IntoIterator<Item = T, IntoIter = impl DoubleEndedIterator<Item = T>>,
    mut g: impl FnMut(&T) -> &K,
    cb: &mut impl DiffCallback<S, T>,
) {
    let (mut a, mut b) = (a.into_iter().de_peekable(), b.into_iter().de_peekable());

    // Sync nodes with same key at start
    while a
        .peek()
        .and_then(|a| b.peek().filter(|&b| f(a) == g(b)))
        .is_some()
    {
        cb.unchanged(a.next().unwrap(), b.next().unwrap());
    }

    // Sync nodes with same key at end
    while a
        .peek_back()
        .and_then(|a| b.peek_back().filter(|&b| f(a) == g(b)))
        .is_some()
    {
        cb.unchanged(a.next_back().unwrap(), b.next_back().unwrap());
    }

    if a.peek().is_none() {
        return b.rev().for_each(|x| cb.inserted(x)); // If all of a was synced add remaining from b
    } else if b.peek().is_none() {
        return a.for_each(|x| cb.removed(x)); // If all of b was synced remove remaining from a
    }

    let (b, mut sources): (Vec<_>, Vec<_>) = b.map(|x| (x, None)).unzip();
    let (mut last_j, mut moved) = (0, false);
    // Associate elements in `a` to their counterparts in `b`, or remove if nonexistant
    let assoc = |(i, (j, a_elem)): (_, (Option<usize>, _))| {
        if let Some(j) = j {
            debug_assert!(sources[j].is_none(), "Duplicate key"); // Catch some instances of dupes
            sources[j] = Some((i, a_elem));

            if j < last_j {
                moved = true;
            }
            last_j = j;
        } else {
            cb.removed(a_elem);
        }
    };
    // If size is small just loop through
    if b.len() < 4 || a.size_hint().1.map_or(false, |hi| hi | b.len() < 32) {
        a.map(|a_elem| (b.iter().position(|b_elem| f(&a_elem) == g(b_elem)), a_elem))
            .enumerate()
            .for_each(assoc);
    } else {
        // Map of keys in b to their respective indices
        let key_index: FxHashMap<_, _> = b.iter().enumerate().map(|(j, ref x)| (g(x), j)).collect();
        a.map(|a_elem| (key_index.get(&f(&a_elem)).copied(), a_elem))
            .enumerate()
            .for_each(assoc);
    }

    if moved {
        // Find longest sequence that can remain stationary
        let mut seq = sources
            .longest_increasing_subsequence_by(
                |a, b| a.as_ref().unwrap().0.cmp(&b.as_ref().unwrap().0),
                Option::is_some,
            )
            .into_iter()
            .rev()
            .peekable();
        for (i, (b, source)) in b.into_iter().zip(sources).enumerate().rev() {
            if let Some((_, a)) = source {
                if Some(&i) == seq.peek() {
                    seq.next();
                    cb.unchanged(a, b);
                } else {
                    cb.moved(a, b);
                }
            } else {
                cb.inserted(b);
            }
        }
    } else {
        for (b, source) in b.into_iter().zip(sources).rev() {
            if let Some((_, a)) = source {
                cb.unchanged(a, b);
            } else {
                cb.inserted(b);
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn powerset<T: Clone>(a: &[T]) -> Vec<Vec<T>> {
        (0..2usize.pow(a.len() as u32))
            .map(|i| {
                a.iter()
                    .enumerate()
                    .filter(|&(t, _)| (i >> t) % 2 == 1)
                    .map(|(_, element)| element.clone())
                    .collect()
            })
            .collect()
    }

    fn run_diff<T: Copy + Eq + Hash>(a: &[T], b: &[T]) -> Vec<T> {
        struct Cb<T> {
            v: Vec<T>,
            idx: usize,
            last_add_one: usize,
        }
        impl<T: Copy + Eq> DiffCallback<(usize, &T), (usize, &T)> for Cb<T> {
            fn inserted(&mut self, (_j, new): (usize, &T)) {
                self.v.insert(self.idx, *new);
            }
            fn removed(&mut self, (_i, old): (usize, &T)) {
                let remove_idx = self.v.iter().position(|x| x == old).unwrap();
                self.v.remove(remove_idx);
                if remove_idx < self.idx {
                    self.idx -= 1;
                }
            }
            fn unchanged(&mut self, (i, _old): (usize, &T), (j, new): (usize, &T)) {
                if i == self.last_add_one && i == j {
                    self.last_add_one += 1;
                } else {
                    self.idx = self.v.iter().position(|x| x == new).unwrap();
                }
            }
            fn moved(&mut self, (_i, old): (usize, &T), (_j, new): (usize, &T)) {
                let remove_idx = self.v.iter().position(|x| x == old).unwrap();
                self.v.remove(remove_idx);
                if remove_idx < self.idx {
                    self.idx -= 1;
                }
                self.v.insert(self.idx, *new);
            }
        }
        let mut cb = Cb {
            v: a.to_vec(),
            idx: a.len(),
            last_add_one: 0,
        };
        diff_by_key(
            a.iter().enumerate(),
            |x| x.1,
            b.iter().enumerate(),
            |x| x.1,
            &mut cb,
        );
        cb.v
    }

    #[test]
    fn test_diff_powerset_seven() {
        let (a, b): (Vec<_>, Vec<_>) = ((0..7).collect(), vec![5, 3, 6, 1, 2, 4, 0]);
        for a in powerset(&a) {
            for b in powerset(&b) {
                let v = run_diff(&a, &b);
                assert_eq!(v, b);
            }
        }
    }

    #[test]
    fn len_zero() {
        assert!(<[i32]>::longest_increasing_subsequence(&[]).is_empty());
    }

    #[test]
    fn len_one() {
        assert_eq!(([5, 4, 3, 2, 1]).longest_increasing_subsequence().len(), 1);
        assert_eq!([0, 0, 0, 0].longest_increasing_subsequence().len(), 1);
    }

    #[test]
    fn lis_test() {
        assert_eq!(
            [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15].longest_increasing_subsequence(),
            [0, 4, 6, 9, 13, 15]
        );
        assert_eq!(
            [2, 3, 4, 3, 5].longest_increasing_subsequence(),
            [0, 1, 2, 4]
        );
    }
}
