use crate::base::traits::core::Async;

pub trait HasError: Async {
    type Error: Async;
}
