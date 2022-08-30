use alloc::sync::Arc;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

use super::telemetry::{CosmosTelemetry, TelemetryState};
use opentelemetry::global;
use std::collections::HashMap;
use std::sync::Mutex;

#[derive(Clone)]
pub struct CosmosChainContext<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
    pub telemetry: CosmosTelemetry,
}

impl<Chain> CosmosChainContext<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: CosmosRuntimeContext) -> Self {
        let telemetry_state = Arc::new(Mutex::new(TelemetryState {
            meter: global::meter("hermes"),
            counters: HashMap::new(),
        }));

        Self {
            chain,
            runtime: OfaRuntimeContext::new(runtime),
            telemetry: CosmosTelemetry::new(telemetry_state),
        }
    }
}
