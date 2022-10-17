use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;

use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::runtime::CosmosRuntimeContext;

#[derive(Clone)]
pub struct CosmosRelayWrapper<Relay: CosmosRelay> {
    pub relay: Arc<Relay>,
    pub src_chain: OfaChainWrapper<CosmosChainWrapper<Relay::SrcChain>>,
    pub dst_chain: OfaChainWrapper<CosmosChainWrapper<Relay::DstChain>>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
}

impl<Relay: CosmosRelay> CosmosRelayWrapper<Relay> {
    pub fn new(relay: Arc<Relay>, runtime: CosmosRuntimeContext) -> Self {
        let src_chain = OfaChainWrapper::new(CosmosChainWrapper::new(
            relay.src_chain().clone(),
            runtime.clone(),
        ));

        let dst_chain = OfaChainWrapper::new(CosmosChainWrapper::new(
            relay.dst_chain().clone(),
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
