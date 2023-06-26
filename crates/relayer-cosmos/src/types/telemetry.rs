use alloc::sync::Arc;
use std::collections::HashMap;
use std::sync::Mutex;

use ibc_relayer_all_in_one::one_for_all::traits::telemetry::OfaTelemetry;
use ibc_relayer_components_extra::telemetry::traits::metrics::HasLabel;
use opentelemetry::{
    global,
    metrics::{Counter, Meter, Unit, UpDownCounter, ValueRecorder},
    KeyValue,
};

pub struct TelemetryState {
    pub meter: Meter,
    pub counters: HashMap<String, Counter<u64>>,
    pub value_recorders: HashMap<String, ValueRecorder<u64>>,
    pub updown_counters: HashMap<String, UpDownCounter<i64>>,
}

pub struct CosmosTelemetry {
    pub telemetry_state: Arc<Mutex<TelemetryState>>,
}

impl CosmosTelemetry {
    pub fn new(telemetry_state: TelemetryState) -> Self {
        Self {
            telemetry_state: Arc::new(Mutex::new(telemetry_state)),
        }
    }
}

impl Default for CosmosTelemetry {
    fn default() -> Self {
        Self::new(TelemetryState {
            meter: global::meter("hermes"),
            counters: HashMap::new(),
            value_recorders: HashMap::new(),
            updown_counters: HashMap::new(),
        })
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
