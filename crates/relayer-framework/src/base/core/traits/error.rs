use core::fmt::Debug;

use crate::base::core::traits::sync::Async;

pub trait HasError: Async {
    type Error: Async + Debug;
}

pub trait InjectError<E>: HasError {
    fn inject_error(e: E) -> Self::Error;
}
