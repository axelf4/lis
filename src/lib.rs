/// Returns the indices of the longest increasing subsequence in `a`.
///
/// # Example
///
/// ```
/// use lis::longest_increasing_subsequence;
/// assert_eq!(longest_increasing_subsequence(&[2, 1, 4, 3, 5]), [1, 3, 4]);
/// ```
pub fn longest_increasing_subsequence<T: PartialOrd>(a: &[T]) -> Vec<usize> {
    let mut p = vec![0; a.len()];
    let mut result = vec![0];

    for i in 1..a.len() {
        let k = &a[i];

        // Test whether k can be used to extend current sequence
        let j = *result.last().unwrap();
        if &a[j] < k {
            p[i] = j;
            result.push(i);
            continue;
        }

        // Binary search
        let (mut lo, mut hi) = (0, result.len() - 1);
        while lo < hi {
            let mid = (lo + hi) / 2;
            if &a[result[mid]] < k {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if k < &a[result[lo]] {
            if lo > 0 {
                p[i] = result[lo - 1];
            }
            result[lo] = i;
        }
    }

    let mut v = *result.last().unwrap();
    for i in (0..result.len()).rev() {
        result[i] = v;
        v = p[v];
    }
    result
}

#[cfg(test)]
mod tests {
    use longest_increasing_subsequence;

    #[test]
    fn len_one() {
        assert_eq!(longest_increasing_subsequence(&[5, 4, 3, 2, 1]).len(), 1);
        assert_eq!(longest_increasing_subsequence(&[0, 0, 0, 0]).len(), 1);
    }

    #[test]
    fn lis_test() {
        assert_eq!(longest_increasing_subsequence(&[2, 1, 4, 3, 5]), [1, 3, 4]);
        assert_eq!(longest_increasing_subsequence(&[2, 3, 4, 3, 5]), [0, 1, 2, 4]);
    }
}
