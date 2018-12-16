use std::cmp::Ordering::{self, Greater, Less};

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

#[cfg(test)]
mod tests {
    use super::*;

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
