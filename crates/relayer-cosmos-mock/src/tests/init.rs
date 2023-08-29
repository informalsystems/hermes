use basecoin_store::impls::InMemoryStore;
use ibc::core::ics24_host::identifier::ChainId;
use std::str::FromStr;
use std::sync::Arc;

use crate::contexts::basecoin::MockBasecoin;
use crate::contexts::chain::MockCosmosContext;
use crate::contexts::relay::MockCosmosRelay;
use crate::contexts::runtime::MockClock;

pub fn mock_basecoin_binary_stand() -> (
    Arc<MockCosmosContext<MockBasecoin<InMemoryStore>>>,
    Arc<MockCosmosContext<MockBasecoin<InMemoryStore>>>,
    MockCosmosRelay<MockBasecoin<InMemoryStore>, MockBasecoin<InMemoryStore>>,
) {
    let clock = Arc::new(MockClock::default());

    // Source chain setup
    let src_chain_id = ChainId::from_str("mock-cosmos-chain-0").expect("never fails");
    let src_chain = Arc::new(MockBasecoin::new_default(src_chain_id));
    src_chain.run();

    let src_chain_ctx = Arc::new(MockCosmosContext::new(src_chain, clock.clone()));
    src_chain_ctx.connect();

    // Destination chain setup
    let dst_chain_id = ChainId::from_str("mock-cosmos-chain-1").expect("never fails");
    let dst_chain = Arc::new(MockBasecoin::new_default(dst_chain_id));
    dst_chain.run();

    let dst_chain_ctx = Arc::new(MockCosmosContext::new(dst_chain, clock.clone()));
    dst_chain_ctx.connect();

    // Relayer setup
    let relayer = MockCosmosRelay::new(src_chain_ctx.clone(), dst_chain_ctx.clone(), clock)
        .expect("failed to build relayer");

    (src_chain_ctx, dst_chain_ctx, relayer)
}
