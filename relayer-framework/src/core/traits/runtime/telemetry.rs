use crate::core::traits::core::Async;
pub trait HasLabel: Async {
    type Label: Async;
    fn new_label(key: &str, value: &str) -> Self::Label;
}
