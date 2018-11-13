use std::cmp::Ordering::{self, Greater, Less};

/// Returns indices of the longest increasing subsequence in `a`.
///
/// This is `O(n log n)` worst-case.
///
/// # Example
///
/// ```
/// use lis::longest_increasing_subsequence;
/// assert_eq!(longest_increasing_subsequence(&[2, 1, 4, 3, 5]), [1, 3, 4]);
/// ```
#[inline]
pub fn longest_increasing_subsequence<T: Ord>(a: &[T]) -> Vec<usize> {
    longest_increasing_subsequence_by(a, |a, b| a.cmp(b))
}

/// Returns indices of the longest increasing subsequence in `a` with a comparator function.
///
/// # Example
///
/// ```
/// use lis::longest_increasing_subsequence_by;
/// assert_eq!(longest_increasing_subsequence_by(&[2, 1, 4, 3, 5], |a, b| a.cmp(b)), [1, 3, 4]);
/// ```
pub fn longest_increasing_subsequence_by<T, F>(a: &[T], mut f: F) -> Vec<usize>
where
    F: FnMut(&T, &T) -> Ordering,
{
    if a.is_empty() {
        return Vec::new();
    }
    let (mut p, mut m) = (vec![0; a.len()], Vec::with_capacity(a.len()));
    m.push(0);

    for i in 1..a.len() {
        // Test whether a[i] can extend the current sequence
        if f(&a[*m.last().unwrap()], &a[i]) == Less {
            p[i] = *m.last().unwrap();
            m.push(i);
            continue;
        }

        // Binary search for largest j ≤ m.len() such that a[m[j]] < a[i]
        let j = match m.binary_search_by(|&j| f(&a[j], &a[i]).then(Greater)) {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn len_zero() {
        assert!(longest_increasing_subsequence::<i32>(&[]).is_empty());
    }

    #[test]
    fn len_one() {
        assert_eq!(longest_increasing_subsequence(&[5, 4, 3, 2, 1]).len(), 1);
        assert_eq!(longest_increasing_subsequence(&[0, 0, 0, 0]).len(), 1);
    }

    #[test]
    fn lis_test() {
        assert_eq!(
            longest_increasing_subsequence(&[0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]),
            [0, 4, 6, 9, 13, 15]
        );
        assert_eq!(
            longest_increasing_subsequence(&[2, 3, 4, 3, 5]),
            [0, 1, 2, 4]
        );
    }
}
