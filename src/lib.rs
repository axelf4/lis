/// Returns the indices of the longest increasing subsequence in `a`.
///
/// This is O(n log n).
///
/// # Panics
///
/// Panics if `a.len()` is zero.
///
/// # Example
///
/// ```
/// use lis::longest_increasing_subsequence;
/// assert_eq!(longest_increasing_subsequence(&[2, 1, 4, 3, 5]), [1, 3, 4]);
/// ```
pub fn longest_increasing_subsequence<T: PartialOrd>(a: &[T]) -> Vec<usize> {
    let (mut p, mut m) = (vec![0; a.len()], vec![0; a.len()]);
    let mut l = 1;
    for i in 1..a.len() {
        // Test whether a[i] can extend the current sequence
        let j = m[l - 1];
        if a[j] < a[i] {
            p[i] = j;
            m[l] = i;
            l += 1;
            continue;
        }

        // Binary search
        let (mut lo, mut hi) = (0, l - 1);
        while lo < hi {
            let mid = (lo + hi) / 2;
            if a[m[mid]] < a[i] {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo > 0 {
            p[i] = m[lo - 1];
        }
        m[lo] = i;
    }

    // Reconstruct the longest increasing subsequence
    let mut k = m[l - 1];
    unsafe {
        m.set_len(l);
    }
    for i in (0..l).rev() {
        m[i] = k;
        k = p[k];
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn len_zero() {
        longest_increasing_subsequence::<i32>(&[]);
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
