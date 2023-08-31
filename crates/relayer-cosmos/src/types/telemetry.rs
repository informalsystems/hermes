use alloc::sync::Arc;
use std::collections::HashMap;
use std::sync::Mutex;

use opentelemetry::{
    global,
    metrics::{Counter, Meter, UpDownCounter, ValueRecorder},
};

#[derive(Clone)]
pub struct CosmosTelemetry {
    pub meter: Arc<Meter>,

    pub counters: Arc<Mutex<HashMap<String, Counter<u64>>>>,

    pub value_recorders: Arc<Mutex<HashMap<String, ValueRecorder<u64>>>>,

    pub updown_counters: Arc<Mutex<HashMap<String, UpDownCounter<i64>>>>,
}

impl Default for CosmosTelemetry {
    fn default() -> Self {
        Self {
            meter: Arc::new(global::meter("hermes")),
            counters: Arc::new(Mutex::new(HashMap::new())),
            value_recorders: Arc::new(Mutex::new(HashMap::new())),
            updown_counters: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}
