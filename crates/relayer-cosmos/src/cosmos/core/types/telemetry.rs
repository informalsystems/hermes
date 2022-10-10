use alloc::sync::Arc;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetry;
use ibc_relayer_framework::full::telemetry::traits::telemetry::HasLabel;
use opentelemetry::metrics::Unit;
use opentelemetry::{
    metrics::{Counter, Meter, UpDownCounter, ValueRecorder},
    KeyValue,
};
use std::collections::HashMap;
use std::sync::Mutex;

pub struct TelemetryState {
    pub meter: Meter,
    pub counters: HashMap<String, Counter<u64>>,
    pub value_recorders: HashMap<String, ValueRecorder<u64>>,
    pub updown_counters: HashMap<String, UpDownCounter<i64>>,
}

#[derive(Clone)]
pub struct CosmosTelemetry {
    pub telemetry_state: Arc<Mutex<TelemetryState>>,
}

impl CosmosTelemetry {
    pub fn new(telemetry_state: Arc<Mutex<TelemetryState>>) -> Self {
        Self { telemetry_state }
    }
}

impl HasLabel for CosmosTelemetry {
    type Label = KeyValue;
    fn new_label(key: &str, value: &str) -> Self::Label {
        KeyValue::new(key.to_string(), value.to_string())
    }
}

impl OfaTelemetry for CosmosTelemetry {
    type CounterType = u64;
    type ValueRecorderType = u64;
    type UpDownCounterType = i64;
    type Unit = Unit;

    fn update_counter_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::CounterType,
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

    fn update_value_recorder_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::ValueRecorderType,
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

    fn update_up_down_counter_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: Self::UpDownCounterType,
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
