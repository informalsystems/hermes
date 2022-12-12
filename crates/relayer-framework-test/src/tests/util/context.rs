use alloc::string::{String, ToString};
use std::sync::Arc;

use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;
use crate::relayer_mock::contexts::relay::MockRelayContext;
use crate::relayer_mock::util::clock::MockClock;
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::common::one_for_all::types::relay::OfaRelayWrapper;

pub fn build_mock_relay_context() -> (
    OfaRelayWrapper<MockRelayContext>,
    Arc<OfaChainWrapper<MockChainContext>>,
    Arc<OfaChainWrapper<MockChainContext>>,
) {
    let clock = Arc::new(MockClock::default());
    let runtime = MockRuntimeContext::new(clock.clone());
    let src_chain = Arc::new(OfaChainWrapper {
        chain: MockChainContext::new("chain1".to_string(), clock.clone()),
    });
    let dst_chain = Arc::new(OfaChainWrapper {
        chain: MockChainContext::new("chain2".to_string(), clock),
    });
    let mock_relay = MockRelayContext::new(
        src_chain.clone(),
        dst_chain.clone(),
        String::from("client_src_to_dst"),
        String::from("client_dst_to_src"),
        runtime,
    );

    let relay = OfaRelayWrapper::new(mock_relay);

    (relay, src_chain, dst_chain)
}
