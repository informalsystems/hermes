use ibc::core::ics24_host::identifier::ChainId;
use std::str::FromStr;

use crate::contexts::builder::MockCosmosBuilder;

pub fn init_binary_stand() -> MockCosmosBuilder {
    let mut builder = MockCosmosBuilder::new_default();

    let src_chain = builder.build_chain(ChainId::from_str("mock-cosmos-chain-0").unwrap());

    let dst_chain = builder.build_chain(ChainId::from_str("mock-cosmos-chain-1").unwrap());

    builder.build_relayer(src_chain, dst_chain);

    builder.spawn_chains();

    builder
}
