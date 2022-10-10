use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::cosmos::core::types::runtime::CosmosRuntimeContext;
use crate::cosmos::core::types::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
}

impl<Chain> CosmosChainWrapper<Chain> {
    pub fn new(
        chain: Arc<Chain>,
        runtime: CosmosRuntimeContext,
        telemetry: CosmosTelemetry,
    ) -> Self {
        Self {
            chain,
            runtime: OfaRuntimeContext::new(runtime),
            telemetry: OfaTelemetryWrapper::new(telemetry),
        }
    }
}
