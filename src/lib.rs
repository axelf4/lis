#![feature(generators, generator_trait)]

use rustc_hash::FxHashMap;
use std::cmp::Ordering::{self, Greater, Less};
use std::hash::Hash;
use std::ops::Generator;

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
    fn de_peekable(self) -> DePeekable<Self>
    where
        Self: Sized + DoubleEndedIterator,
    {
        DePeekable {
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
struct DePeekable<I: Iterator> {
    iter: I,
    front: Option<Option<I::Item>>,
    back: Option<Option<I::Item>>,
}

impl<I: Iterator> DePeekable<I> {
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

impl<I: Iterator> Iterator for DePeekable<I> {
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

impl<I: DoubleEndedIterator> DoubleEndedIterator for DePeekable<I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back
            .take()
            .unwrap_or_else(|| self.iter.next_back())
            .or_else(|| self.front.take().unwrap_or(None))
    }
}

impl<I: std::iter::ExactSizeIterator> std::iter::ExactSizeIterator for DePeekable<I> {}
impl<I: std::iter::FusedIterator> std::iter::FusedIterator for DePeekable<I> {}

/// A fragment of a diff.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum DiffAction<T> {
    /// The new element was inserted.
    Insert(T),
    /// The element stayed in place. Stores the old and new element, in that order.
    Unchanged(T, T),
    /// The element was moved. Stores the old and new element, in that order.
    Move(T, T),
    /// The old element was removed.
    Remove(T),
}

/// Computes the difference between the two iterators with a key extraction function.
///
/// Keys have to be unique. Returns removals in forward order and insertions/moves in reverse order.
/// Guaranteed not to allocate if the changeset is entirely contiguous insertions or removals.
/// Result stores `T`:s instead of indices; use [enumerate] if preferable.
///
/// # Panics
///
/// May panic if `a` contains duplicate keys.
///
/// # Safety
/// Moving the returned generator after it has resumed would invalidate the interior reference.
///
/// [enumerate]: std::iter::Iterator::enumerate
pub fn diff_by_key<I: IntoIterator, T: Eq + Hash, F>(
    a: I,
    b: I,
    mut f: F,
) -> impl Generator<Yield = DiffAction<I::Item>, Return = ()>
where
    I::IntoIter: DoubleEndedIterator,
    F: FnMut(&I::Item) -> &T,
{
    static move || {
        let (mut a, mut b) = (a.into_iter().de_peekable(), b.into_iter().de_peekable());

        // Sync nodes with same key at start
        while a
            .peek()
            .and_then(|a| b.peek().filter(|&b| f(a) == f(b)))
            .is_some()
        {
            yield DiffAction::Unchanged(a.next().unwrap(), b.next().unwrap());
        }

        // Sync nodes with same key at end
        while a
            .peek_back()
            .and_then(|a| b.peek_back().filter(|&b| f(a) == f(b)))
            .is_some()
        {
            yield DiffAction::Unchanged(a.next_back().unwrap(), b.next_back().unwrap());
        }

        if a.peek().is_none() {
            // If all of a was synced add remaining from b
            for x in b.rev() {
                yield DiffAction::Insert(x);
            }
        } else if b.peek().is_none() {
            // If all of b was synced remove remaining from a
            for x in a {
                yield DiffAction::Remove(x);
            }
        } else {
            let (b, mut sources): (Vec<_>, Vec<_>) = b.map(|x| (x, None)).unzip();
            // Map of keys in b to their respective indices
            let key_index: FxHashMap<_, _> =
                b.iter().enumerate().map(|(j, ref x)| (f(x), j)).collect();

            // Associate elements in `a` to their counterpart in `b`, or remove if non-existant
            let (mut last_j, mut moved) = (0, false);
            for (i, a_elem) in a.enumerate() {
                if let Some(&j) = key_index.get(&f(&a_elem)) {
                    debug_assert!(sources[j].is_none(), "Duplicate key"); // Catch some instances of dupes
                    sources[j] = Some((i, a_elem));

                    if j < last_j {
                        moved = true;
                    } else {
                        last_j = j;
                    }
                } else {
                    yield DiffAction::Remove(a_elem);
                }
            }

            if moved {
                // Find longest sequence that can remain stationary
                let mut seq = sources
                    .longest_increasing_subsequence_by(
                        |a, b| a.as_ref().unwrap().0.cmp(&b.as_ref().unwrap().0),
                        |x| x.is_some(),
                    )
                    .into_iter()
                    .rev()
                    .peekable();
                for (i, (b, source)) in b.into_iter().zip(sources).enumerate().rev() {
                    yield if let Some((_, a)) = source {
                        if Some(&i) == seq.peek() {
                            seq.next();
                            DiffAction::Unchanged(a, b)
                        } else {
                            DiffAction::Move(a, b)
                        }
                    } else {
                        DiffAction::Insert(b)
                    };
                }
            } else {
                for (b, source) in b.into_iter().zip(sources).rev() {
                    yield if let Some((_, a)) = source {
                        DiffAction::Unchanged(a, b)
                    } else {
                        DiffAction::Insert(b)
                    };
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::GeneratorState;

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
        let mut v = a.to_vec();
        let mut generator = diff_by_key(a.iter().enumerate(), b.iter().enumerate(), |x| x.1);
        let mut idx = v.len();
        let mut last_add_one = 0;

        while let GeneratorState::Yielded(action) = unsafe { generator.resume() } {
            match action {
                DiffAction::Insert(i) => {
                    v.insert(idx, *i.1);
                }
                DiffAction::Move(i, j) => {
                    let remove_idx = v.iter().position(|x| x == i.1).unwrap();
                    v.remove(remove_idx);
                    if remove_idx < idx {
                        idx -= 1;
                    }
                    v.insert(idx, *j.1);
                }
                DiffAction::Remove(i) => {
                    let remove_idx = v.iter().position(|x| x == i.1).unwrap();
                    v.remove(remove_idx);
                    if remove_idx < idx {
                        idx -= 1;
                    }
                }
                DiffAction::Unchanged(i, j) => {
                    if i.0 == last_add_one && i.0 == j.0 {
                        last_add_one += 1;
                    } else {
                        idx = v.iter().position(|x| x == j.1).unwrap();
                    }
                }
            }
        }
        v
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
