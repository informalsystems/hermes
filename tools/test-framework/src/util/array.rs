/*!
   Helpers for manipulating fixed-sized arrays.
*/

use eyre::eyre;

use crate::error::Error;

/**
   Converts a dynamic-sized vector `Vec<T>` into a fixed-sized array
   `[T; SIZE]`. Fails if the vector is not the same length as `SIZE`.
*/
pub fn try_into_array<T, const SIZE: usize>(list: Vec<T>) -> Result<[T; SIZE], Error> {
    list.try_into()
        .map_err(|_| Error::generic(eyre!("vector is not of length {}", SIZE)))
}

/**
   Converts a fixed-sized nested array `[[T; SIZE]; SIZE]` into a nested
   vector `Vec<Vec<T>>`.
*/
pub fn into_nested_vec<T, const SIZE: usize>(array: [[T; SIZE]; SIZE]) -> Vec<Vec<T>> {
    array.map(|array_b| array_b.into()).into()
}
