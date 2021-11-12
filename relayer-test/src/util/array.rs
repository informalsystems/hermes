use core::convert::TryInto;
use eyre::eyre;

use crate::error::Error;

pub fn try_into_array<T, const SIZE: usize>(list: Vec<T>) -> Result<[T; SIZE], Error> {
    list.try_into()
        .map_err(|_| eyre!("vector is not of length {}", SIZE))
}

pub fn try_into_nested_array<T, const SIZE: usize>(
    list: Vec<Vec<T>>,
) -> Result<[[T; SIZE]; SIZE], Error> {
    let list_a = list
        .into_iter()
        .map(try_into_array)
        .collect::<Result<Vec<_>, _>>()?;

    try_into_array(list_a)
}

pub fn into_nested_vec<T, const SIZE: usize>(array: [[T; SIZE]; SIZE]) -> Vec<Vec<T>> {
    array.map(|array_b| array_b.into()).into()
}

pub fn map_nested_array<T, R, const SIZE: usize>(
    array: [[T; SIZE]; SIZE],
    mapper: impl Fn(T) -> Result<R, Error>,
) -> Result<[[R; SIZE]; SIZE], Error> {
    let mapped = into_nested_vec(array)
        .into_iter()
        .map(|inner| {
            inner
                .into_iter()
                .map(&mapper)
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    try_into_nested_array(mapped)
}

pub fn assert_same_dimension<T>(size: usize, list: &Vec<Vec<T>>) -> Result<(), Error> {
    if list.len() != size {
        return Err(eyre!(
            "expect nested vector to have the dimension {} x {}",
            size,
            size
        ));
    }

    for list_b in list.iter() {
        if list_b.len() != size {
            return Err(eyre!(
                "expect nested vector to have the dimension {} x {}",
                size,
                size
            ));
        }
    }

    Ok(())
}
