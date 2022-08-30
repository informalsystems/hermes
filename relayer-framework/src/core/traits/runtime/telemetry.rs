use crate::core::traits::core::Async;

pub trait TelemetryContext: Async {
    type Label: Async;
    type Error: Async; // Needs to be taken out of this trait

    fn new_label(key: &str, value: &str) -> Self::Label;

    fn new_counter(&self, name: &str, description: &str) -> Result<(), Self::Error>;

    fn add_counter(
        &self,
        name: &str,
        count: u64,
        labels: &[Self::Label],
    ) -> Result<(), Self::Error>;
}
