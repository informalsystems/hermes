use alloc::sync::Arc;
use ibc_relayer_framework::core::traits::runtime::telemetry::*;
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

impl HasMetric<TelemetryCounter> for CosmosTelemetry {
    type Value = u64;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: u64,
        description: Option<&str>,
    ) {
        let mut telemetry_state = self.telemetry_state.lock().unwrap();
        if let Some(metric) = telemetry_state.counters.get(name) {
            metric.add(value, labels);
        } else {
            let metric = if let Some(description) = description {
                telemetry_state
                    .meter
                    .u64_counter(name)
                    .with_description(description)
                    .init()
            } else {
                telemetry_state.meter.u64_counter(name).init()
            };
            metric.add(value, labels);
            telemetry_state.counters.insert(name.to_string(), metric);
        }
    }
}

impl HasMetric<TelemetryValueRecorder> for CosmosTelemetry {
    type Value = u64;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: u64,
        description: Option<&str>,
    ) {
        let mut telemetry_state = self.telemetry_state.lock().unwrap();
        if let Some(metric) = telemetry_state.value_recorders.get(name) {
            metric.record(value, labels);
        } else {
            let metric = if let Some(description) = description {
                telemetry_state
                    .meter
                    .u64_value_recorder(name)
                    .with_description(description)
                    .init()
            } else {
                telemetry_state.meter.u64_value_recorder(name).init()
            };
            metric.record(value, labels);
            telemetry_state.value_recorders.insert(name.to_string(), metric);
        }
    }
}

impl HasMetric<TelemetryUpDownCounter> for CosmosTelemetry {
    type Value = i64;

    fn update_metric(
        &self,
        name: &str,
        labels: &[Self::Label],
        value: i64,
        description: Option<&str>,
    ) {
        let mut telemetry_state = self.telemetry_state.lock().unwrap();
        if let Some(metric) = telemetry_state.updown_counters.get(name) {
            metric.add(value, labels);
        } else {
            let metric = if let Some(description) = description {
                telemetry_state
                    .meter
                    .i64_up_down_counter(name)
                    .with_description(description)
                    .init()
            } else {
                telemetry_state.meter.i64_up_down_counter(name).init()
            };
            metric.add(value, labels);
            telemetry_state.updown_counters.insert(name.to_string(), metric);
        }
    }
}

impl BasicTelemetryContext for CosmosTelemetry {}
