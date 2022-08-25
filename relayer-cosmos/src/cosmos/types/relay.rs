use alloc::sync::Arc;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::context::runtime::CosmosRuntimeContext;
use crate::cosmos::traits::relay::CosmosRelay;
use crate::cosmos::types::chain::CosmosChainContext;

#[derive(Clone)]
pub struct CosmosRelayContext<Relay: CosmosRelay> {
    pub relay: Arc<Relay>,
    pub src_chain: OfaChainContext<CosmosChainContext<Relay::SrcChain>>,
    pub dst_chain: OfaChainContext<CosmosChainContext<Relay::SrcChain>>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
}

impl<Relay: CosmosRelay> CosmosRelayContext<Relay> {
    pub fn new(relay: Arc<Relay>, runtime: CosmosRuntimeContext) -> Self {
        let src_chain = OfaChainContext::new(CosmosChainContext::new(
            relay.src_chain().clone(),
            runtime.clone(),
        ));

        let dst_chain = OfaChainContext::new(CosmosChainContext::new(
            relay.src_chain().clone(),
            runtime.clone(),
        ));

        let runtime = OfaRuntimeContext::new(runtime);

        Self {
            relay,
            src_chain,
            dst_chain,
            runtime,
        }
    }
}
