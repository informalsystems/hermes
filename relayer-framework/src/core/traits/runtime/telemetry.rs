use crate::core::traits::core::Async;
use crate::std_prelude::*;

pub trait HasLabel: Async {
    type Label: Async;
    fn new_label(key: &str, value: &str) -> Self::Label;
}

pub trait HasMetric<MetricType: Async, Value: Async>: Async + HasLabel {
    type Metric: Async;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Value,
        description: Option<&str>,
    ) -> ();
}

pub struct TelemetryCounter;
pub struct TelemetryValueRecorder;
pub struct TelemetryUpDownCounter;

pub trait TelemetryContext:
    HasMetric<TelemetryCounter, u64>
    + HasMetric<TelemetryValueRecorder, u64>
    + HasMetric<TelemetryUpDownCounter, i64>
{
}
