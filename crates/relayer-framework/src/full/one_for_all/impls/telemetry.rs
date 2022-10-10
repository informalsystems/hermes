use crate::full::one_for_all::traits::telemetry::{OfaTelemetry, OfaTelemetryWrapper};
use crate::full::telemetry::traits::metrics::{
    HasLabel, HasMetric, TelemetryCounter, TelemetryUpDownCounter, TelemetryValueRecorder,
};

impl<Telemetry: HasLabel> HasLabel for OfaTelemetryWrapper<Telemetry> {
    type Label = Telemetry::Label;
    fn new_label(key: &str, value: &str) -> Self::Label {
        Telemetry::new_label(key, value)
    }
}

impl<Telemetry> HasMetric<TelemetryCounter> for OfaTelemetryWrapper<Telemetry>
where
    Telemetry: OfaTelemetry,
{
    type Value = Telemetry::CounterType;
    type Unit = Telemetry::Unit;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    ) {
        self.telemetry
            .update_counter_metric(name, labels, value, description, unit);
    }
}

impl<Telemetry> HasMetric<TelemetryValueRecorder> for OfaTelemetryWrapper<Telemetry>
where
    Telemetry: OfaTelemetry,
{
    type Value = Telemetry::ValueRecorderType;
    type Unit = Telemetry::Unit;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    ) {
        self.telemetry
            .update_value_recorder_metric(name, labels, value, description, unit);
    }
}

impl<Telemetry> HasMetric<TelemetryUpDownCounter> for OfaTelemetryWrapper<Telemetry>
where
    Telemetry: OfaTelemetry,
{
    type Value = Telemetry::UpDownCounterType;
    type Unit = Telemetry::Unit;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    ) {
        self.telemetry
            .update_up_down_counter_metric(name, labels, value, description, unit);
    }
}
