use crate::traits::core::Async;

pub trait BatchError: Async {
    fn as_batch_error(&self) -> Self;
}
