use core::fmt::Debug;

use crate::base::core::traits::sync::Async;

pub trait HasErrorType: Async {
    type Error: Async + Debug;
}

pub trait InjectError<E>: HasErrorType {
    fn inject_error(e: E) -> Self::Error;
}
