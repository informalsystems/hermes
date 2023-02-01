use crate::core::traits::sync::Async;

pub trait HasError: Async {
    type Error: Async;
}

pub trait InjectError<E>: HasError {
    fn inject_error(error: E) -> Self::Error;
}
