use crate::base::core::traits::sync::Async;

pub trait HasError: Async {
    type Error: Async;
}
