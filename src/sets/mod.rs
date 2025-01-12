use std::{collections::HashSet, hash::Hash};

pub fn are_disjoint<T: std::cmp::Eq + Hash, U: Iterator<Item = HashSet<T>> + Clone>(
    iterator: &U,
) -> bool {
    for (i, left) in iterator.clone().enumerate() {
        for right in iterator.clone().skip(i + 1) {
            if !left.is_disjoint(&right) {
                return false;
            }
        }
    }
    true
}

pub fn union<T: std::cmp::Eq + Hash, U: Iterator<Item = HashSet<T>>>(
    iterator: U,
) -> impl Iterator<Item = T> {
    iterator.flatten()
}

pub fn intersection<T: std::cmp::Eq + Hash + Clone, U: Iterator<Item = HashSet<T>>>(
    mut iterator: U,
) -> impl Iterator<Item = T> {
    let first_set = iterator.next().unwrap_or_else(HashSet::new);

    iterator
        .fold(first_set, |accum, set| {
            accum.intersection(&set).cloned().collect()
        })
        .into_iter()
}

pub fn subtract<T: std::cmp::Eq + Hash>(
    lhs: HashSet<T>,
    rhs: &HashSet<T>,
) -> impl Iterator<Item = T> + use<'_, T> {
    lhs.into_iter().filter(move |elem| !rhs.contains(&elem))
}

pub fn skip_nth<I, T>(iter: I, n: usize) -> impl Iterator<Item = T>
where
    I: IntoIterator<Item = T>,
{
    iter.into_iter().enumerate().filter_map(
        move |(index, item)| {
            if index == n {
                None
            } else {
                Some(item)
            }
        },
    )
}
