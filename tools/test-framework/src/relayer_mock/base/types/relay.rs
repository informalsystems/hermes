use std::{collections::HashMap, sync::Arc};
use tokio::runtime::Runtime;

use ibc_relayer_framework::{
    base::one_for_all::traits::runtime::OfaRuntimeContext,
    common::one_for_all::types::chain::OfaChainWrapper,
};
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::relayer_mock::base::{
    traits::relay::MockRelay,
    types::{chain::MockChainWrapper, runtime::MockRuntimeContext},
};

pub struct MockRelayWrapper<Relay: MockRelay> {
    pub relay: Arc<Relay>,
    pub src_chain: OfaChainWrapper<MockChainWrapper<Relay::SrcChain>>,
    pub dst_chain: OfaChainWrapper<MockChainWrapper<Relay::DstChain>>,
    pub runtime: OfaRuntimeContext<MockRuntimeContext>,
}

impl<Relay> MockRelayWrapper<Relay>
where
    Relay: MockRelay,
{
    pub fn new(relay: Arc<Relay>) -> Self {
        let runtime =
            OfaRuntimeContext::new(TokioRuntimeContext::new(Arc::new(Runtime::new().unwrap())));

        let src_chain = OfaChainWrapper::new(MockChainWrapper::new(
            relay.src_chain().clone(),
            runtime.clone(),
            HashMap::new(),
        ));

        let dst_chain = OfaChainWrapper::new(MockChainWrapper::new(
            relay.dst_chain().clone(),
            runtime.clone(),
            HashMap::new(),
        ));

        Self {
            relay,
            src_chain,
            dst_chain,
            runtime,
        }
    }
}
