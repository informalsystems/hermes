use core::fmt::Debug;

use crate::error::Error;

pub fn assert_eq<T: Eq + Debug>(message: &str, left: &T, right: &T) -> Result<(), Error> {
    if left == right {
        Ok(())
    } else {
        Err(Error::assertion(format!(
            "expect left ({:?}) to be equal to right ({:?}): {}",
            left, right, message
        )))
    }
}

pub fn assert_not_eq<T: Eq + Debug>(message: &str, left: &T, right: &T) -> Result<(), Error> {
    if left != right {
        Ok(())
    } else {
        Err(Error::assertion(format!(
            "expect left ({:?}) to be not equal to right ({:?}): {}",
            left, right, message
        )))
    }
}

pub fn assert_gt<T: Ord + Debug>(message: &str, left: &T, right: &T) -> Result<(), Error> {
    if left > right {
        Ok(())
    } else {
        Err(Error::assertion(format!(
            "expect left ({:?}) to be greater than right ({:?}): {}",
            left, right, message
        )))
    }
}

pub fn assert_err<T: Debug, E: Debug>(message: &str, result: Result<T, E>) -> Result<(), Error> {
    if result.is_err() {
        Ok(())
    } else {
        Err(Error::assertion(format!(
            "expect result ({:?}) to be an error: {}",
            result, message
        )))
    }
}
