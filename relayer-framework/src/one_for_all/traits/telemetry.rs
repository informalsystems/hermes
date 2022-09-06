use crate::core::traits::{core::Async, runtime::telemetry::HasLabel};
pub trait OfaTelemetry: HasLabel {
    type CounterType: Async + From<u64>;
    type ValueRecorderType: Async + From<u64>;
    type UpDownCounterType: Async + From<i64>;
    type Unit: Async;

    fn update_counter_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::CounterType,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    );
    fn update_value_recorder_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::ValueRecorderType,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    );
    fn update_up_down_counter_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::UpDownCounterType,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    );
}

#[derive(Clone)]
pub struct OfaTelemetryWrapper<Telemetry> {
    pub telemetry: Telemetry,
}

impl<Telemetry> OfaTelemetryWrapper<Telemetry> {
    pub fn new(telemetry: Telemetry) -> Self {
        Self { telemetry }
    }
}
