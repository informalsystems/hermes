use basecoin_store::impls::InMemoryStore;
use ibc::core::ics24_host::identifier::ChainId;
use std::str::FromStr;
use std::sync::Arc;

use crate::contexts::basecoin::MockBasecoin;
use crate::contexts::chain::MockCosmosContext;
use crate::contexts::relay::MockCosmosRelay;
use crate::contexts::runtime::MockClock;

pub fn binary_mock_basecoin_stand() -> (
    Arc<MockCosmosContext<MockBasecoin<InMemoryStore>>>,
    Arc<MockCosmosContext<MockBasecoin<InMemoryStore>>>,
    MockCosmosRelay<MockBasecoin<InMemoryStore>, MockBasecoin<InMemoryStore>>,
) {
    let clock = Arc::new(MockClock::default());

    // Source chain setup
    let src_chain_id = ChainId::from_str("mock-cosmos-chain-0").unwrap();
    let src_chain = Arc::new(MockBasecoin::new(src_chain_id, InMemoryStore::default()));
    src_chain.spawn();
    let src_chain_ctx = Arc::new(MockCosmosContext::new(src_chain, clock.clone()));
    src_chain_ctx.subscribe();

    // Destination chain setup
    let dst_chain_id = ChainId::from_str("mock-cosmos-chain-1").unwrap();
    let dst_chain = Arc::new(MockBasecoin::new(dst_chain_id, InMemoryStore::default()));
    dst_chain.spawn();
    let dst_chain_ctx = Arc::new(MockCosmosContext::new(dst_chain, clock.clone()));
    dst_chain_ctx.subscribe();

    // Relayer setup
    let relayer = MockCosmosRelay::new(src_chain_ctx.clone(), dst_chain_ctx.clone(), clock)
        .expect("failed to build relayer");

    (src_chain_ctx, dst_chain_ctx, relayer)
}
