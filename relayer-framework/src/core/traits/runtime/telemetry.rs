use crate::core::traits::core::Async;

pub trait TelemetryContext: Async {
    type Entry: Async;

    fn new_entry(key: &str, value: &str) -> Self::Entry;

    fn add_counter(&self, name: &str, count: u64, labels: &[Self::Entry]);
}
