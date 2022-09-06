use alloc::sync::Arc;
use ibc_relayer_framework::one_for_all::traits::{
    runtime::OfaRuntimeContext, telemetry::OfaTelemetryWrapper,
};

use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

use super::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct CosmosChainContext<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
}

impl<Chain> CosmosChainContext<Chain> {
    pub fn new(
        chain: Arc<Chain>,
        runtime: CosmosRuntimeContext,
        telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    ) -> Self {
        Self {
            chain,
            runtime: OfaRuntimeContext::new(runtime),
            telemetry,
        }
    }
}
