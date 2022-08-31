use alloc::sync::Arc;

use ibc_relayer_framework::core::traits::contexts::error::HasError;
use ibc_relayer_framework::core::traits::runtime::telemetry::TelemetryContext;
use opentelemetry::{
    metrics::{Counter, Meter},
    KeyValue,
};
use std::collections::HashMap;
use std::sync::Mutex;

pub enum TelemetryError {
    FailedToCreateMetric,
    FailedToCreateLabel,
    FailedToUpdateMetric,
}

pub struct TelemetryState {
    pub meter: Meter,
    pub counters: HashMap<String, Counter<u64>>,
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

impl HasError for CosmosTelemetry {
    type Error = TelemetryError;
}

impl TelemetryContext for CosmosTelemetry {
    type Label = KeyValue;

    fn new_label(key: &str, value: &str) -> KeyValue {
        KeyValue::new(key.to_string(), value.to_string())
    }

    fn new_counter(&self, name: &str, description: &str) -> Result<(), Self::Error> {
        let mut telemetry_state = self.telemetry_state.lock().unwrap(); // TODO: Remove unwrap

        let meter = &telemetry_state.meter;
        let metric = meter.u64_counter(name).with_description(description).init();

        telemetry_state
            .counters
            .insert(name.to_string(), metric)
            .ok_or(TelemetryError::FailedToCreateMetric)?;
        Ok(())
    }

    fn add_counter(
        &self,
        name: &str,
        count: u64,
        labels: &[KeyValue],
    ) -> Result<(), TelemetryError> {
        self.telemetry_state
            .lock()
            .unwrap() // TODO: Remove unwrap
            .counters
            .get(name)
            .ok_or(TelemetryError::FailedToUpdateMetric)?
            .add(count, labels);
        Ok(())
    }
}
