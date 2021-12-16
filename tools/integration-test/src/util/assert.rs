use core::fmt::Debug;
use eyre::eyre;

use crate::error::Error;

pub fn assert_eq<T: Eq + Debug>(message: &str, left: &T, right: &T) -> Result<(), Error> {
    if left == right {
        Ok(())
    } else {
        Err(eyre!(
            "expect left ({:?}) to be equal to right ({:?}): {}",
            left,
            right,
            message
        ))
    }
}
