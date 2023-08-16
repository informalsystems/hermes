use ibc_relayer_components_extra::telemetry::traits::metrics::{
    HasLabel, HasMetric, TelemetryCounter, TelemetryUpDownCounter, TelemetryValueRecorder,
};
use opentelemetry::metrics::Unit;
use opentelemetry::KeyValue;

use crate::types::telemetry::CosmosTelemetry;

impl HasLabel for CosmosTelemetry {
    type Label = KeyValue;
    fn new_label(key: &str, value: &str) -> Self::Label {
        KeyValue::new(key.to_string(), value.to_string())
    }
}

impl HasMetric<TelemetryCounter> for CosmosTelemetry {
    type Value = u64;

    type Unit = Unit;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    ) {
        let mut telemetry_state = self.telemetry_state.lock().unwrap();
        if let Some(metric) = telemetry_state.counters.get(name) {
            metric.add(value, labels);
        } else {
            let builder = telemetry_state.meter.u64_counter(name);
            let builder = if let Some(description) = description {
                builder.with_description(description)
            } else {
                builder
            };
            let builder = if let Some(unit) = unit {
                builder.with_unit(unit)
            } else {
                builder
            };
            let metric = builder.init();
            metric.add(value, labels);
            telemetry_state.counters.insert(name.to_string(), metric);
        }
    }
}

impl HasMetric<TelemetryValueRecorder> for CosmosTelemetry {
    type Value = u64;

    type Unit = Unit;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    ) {
        let mut telemetry_state = self.telemetry_state.lock().unwrap();
        if let Some(metric) = telemetry_state.value_recorders.get(name) {
            metric.record(value, labels);
        } else {
            let builder = telemetry_state.meter.u64_value_recorder(name);
            let builder = if let Some(description) = description {
                builder.with_description(description)
            } else {
                builder
            };
            let builder = if let Some(unit) = unit {
                builder.with_unit(unit)
            } else {
                builder
            };
            let metric = builder.init();
            metric.record(value, labels);
            telemetry_state
                .value_recorders
                .insert(name.to_string(), metric);
        }
    }
}

impl HasMetric<TelemetryUpDownCounter> for CosmosTelemetry {
    type Value = i64;

    type Unit = Unit;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::Value,
        description: Option<&str>,
        unit: Option<Self::Unit>,
    ) {
        let mut telemetry_state = self.telemetry_state.lock().unwrap();
        if let Some(metric) = telemetry_state.updown_counters.get(name) {
            metric.add(value, labels);
        } else {
            let builder = telemetry_state.meter.i64_up_down_counter(name);
            let builder = if let Some(description) = description {
                builder.with_description(description)
            } else {
                builder
            };
            let builder = if let Some(unit) = unit {
                builder.with_unit(unit)
            } else {
                builder
            };
            let metric = builder.init();
            metric.add(value, labels);
            telemetry_state
                .updown_counters
                .insert(name.to_string(), metric);
        }
    }
}
