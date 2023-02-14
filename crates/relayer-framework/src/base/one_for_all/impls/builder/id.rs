use async_trait::async_trait;

use crate::base::builder::traits::id::{HasTargetChainIds, HasTargetClientIds};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{
    ChainIdA, ChainIdB, ClientIdA, ClientIdB, OfaBuilder,
};
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;

#[async_trait]
impl<Builder> HasTargetChainIds for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    fn chain_id_a(&self) -> ChainIdA<Builder> {
        self.builder.chain_id_a()
    }

    fn chain_id_b(&self) -> ChainIdB<Builder> {
        self.builder.chain_id_b()
    }
}

#[async_trait]
impl<Builder> HasTargetClientIds for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    fn client_id_a(&self) -> ClientIdA<Builder> {
        self.builder.client_id_a()
    }

    fn client_id_b(&self) -> ClientIdB<Builder> {
        self.builder.client_id_b()
    }
}
