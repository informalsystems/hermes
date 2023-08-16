use alloc::sync::Arc;
use std::collections::HashMap;
use std::sync::Mutex;

use opentelemetry::{
    global,
    metrics::{Counter, Meter, UpDownCounter, ValueRecorder},
};

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
