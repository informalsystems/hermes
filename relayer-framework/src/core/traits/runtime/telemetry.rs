use crate::core::traits::core::Async;
use crate::std_prelude::*;

pub trait HasLabel: Async {
    type Label: Async;
    fn new_label(key: &str, value: &str) -> Self::Label;
}

pub trait HasMetric<MetricType: Async>: Async + HasLabel {
    type Value: Async;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
    );
}

pub struct TelemetryCounter;
pub struct TelemetryValueRecorder;
pub struct TelemetryUpDownCounter;

pub trait BasicTelemetryContext:
    HasMetric<TelemetryCounter, Value = u64>
    + HasMetric<TelemetryValueRecorder, Value = u64>
    + HasMetric<TelemetryUpDownCounter, Value = i64>
{
}
