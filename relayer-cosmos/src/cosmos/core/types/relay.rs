use alloc::sync::Arc;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::cosmos::core::impls::filters::CosmosChannelFilter;
use crate::cosmos::core::traits::relay::CosmosRelay;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

use crate::cosmos::core::types::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct CosmosRelayContext<Relay: CosmosRelay> {
    pub relay: Arc<Relay>,
    pub src_chain: OfaChainContext<CosmosChainContext<Relay::SrcChain>>,
    pub dst_chain: OfaChainContext<CosmosChainContext<Relay::DstChain>>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    pub filter: CosmosChannelFilter,
}

impl<Relay: CosmosRelay> CosmosRelayContext<Relay> {
    pub fn new(
        relay: Arc<Relay>,
        runtime: CosmosRuntimeContext,
        telemetry: CosmosTelemetry,
        filter: CosmosChannelFilter,
    ) -> Self {
        let src_chain = OfaChainContext::new(CosmosChainContext::new(
            relay.src_chain().clone(),
            runtime.clone(),
            telemetry.clone(),
        ));

        let dst_chain = OfaChainContext::new(CosmosChainContext::new(
            relay.dst_chain().clone(),
            runtime.clone(),
            telemetry.clone(),
        ));

        let runtime = OfaRuntimeContext::new(runtime);

        Self {
            relay,
            src_chain,
            dst_chain,
            runtime,
            telemetry: OfaTelemetryWrapper::new(telemetry),
            filter,
        }
    }
}
