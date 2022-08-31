use crate::core::traits::contexts::error::HasError;
use crate::core::traits::core::Async;

pub trait TelemetryContext: Async + HasError {
    type Label: Async;

    fn new_label(key: &str, value: &str) -> Self::Label;

    fn new_counter(&self, name: &str, description: &str) -> Result<(), Self::Error>;

    fn add_counter(
        &self,
        name: &str,
        count: u64,
        labels: &[Self::Label],
    ) -> Result<(), Self::Error>;
}
