use alloc::string::{String, ToString};
use std::sync::Arc;
use tokio::runtime::Runtime;

use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;
use crate::relayer_mock::contexts::relay::MockRelayContext;
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::common::one_for_all::types::relay::OfaRelayWrapper;

pub fn build_mock_relay_context() -> (
    OfaRelayWrapper<MockRelayContext>,
    Arc<OfaChainWrapper<MockChainContext>>,
    Arc<OfaChainWrapper<MockChainContext>>,
) {
    let runtime = MockRuntimeContext::new(Arc::new(Runtime::new().unwrap()));
    let src_chain = Arc::new(OfaChainWrapper {
        chain: MockChainContext::new("chain1".to_string()),
    });
    let dst_chain = Arc::new(OfaChainWrapper {
        chain: MockChainContext::new("chain2".to_string()),
    });
    let mock_relay = MockRelayContext::new(
        src_chain.clone(),
        dst_chain.clone(),
        String::from("client_a"),
        String::from("client_b"),
        runtime,
    );

    let relay = OfaRelayWrapper::new(mock_relay);

    (relay, src_chain, dst_chain)
}
