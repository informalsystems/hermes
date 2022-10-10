use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::traits::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::base::impls::filters::FilterWrapper;
use crate::cosmos::base::traits::filter::CosmosFilter;
use crate::cosmos::base::traits::relay::CosmosRelay;
use crate::cosmos::base::types::chain::CosmosChainWrapper;
use crate::cosmos::base::types::runtime::CosmosRuntimeContext;

#[derive(Clone)]
pub struct CosmosRelayWrapper<Relay: CosmosRelay, Filter: CosmosFilter + Clone> {
    pub relay: Arc<Relay>,
    pub src_chain: OfaChainWrapper<CosmosChainWrapper<Relay::SrcChain>>,
    pub dst_chain: OfaChainWrapper<CosmosChainWrapper<Relay::DstChain>>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
    pub filter: FilterWrapper<Filter>,
}

impl<Relay: CosmosRelay, Filter: CosmosFilter + Clone> CosmosRelayWrapper<Relay, Filter> {
    pub fn new(relay: Arc<Relay>, runtime: CosmosRuntimeContext, filter: Filter) -> Self {
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
            filter: FilterWrapper::new(filter),
        }
    }
}
