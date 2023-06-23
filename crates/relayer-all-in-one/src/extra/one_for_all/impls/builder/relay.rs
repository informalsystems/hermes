use async_trait::async_trait;
use ibc_relayer_components::builder::impls::cache::BuildWithCache;
use ibc_relayer_components::builder::impls::relay::BuildRelayFromChains;
use ibc_relayer_components::builder::traits::relay::{CanBuildRelay, RelayBuilder};
use ibc_relayer_components::builder::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use ibc_relayer_components_extra::builder::impls::batch::BuildBatchWorker;
use ibc_relayer_components_extra::builder::traits::relay::RelayBuilderWithBatch;

use crate::base::one_for_all::impls::builder::relay::BuildRelayFromChainsWithOfa;
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA, RelayError,
};
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::extra::one_for_all::traits::builder::OfaFullBuilder;
use crate::extra::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::extra::one_for_all::types::builder::OfaFullBuilderWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Builder> CanBuildRelay<RelayAToBTarget> for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_relay(
        &self,
        target: RelayAToBTarget,
        src_chain_id: &ChainIdA<Builder>,
        dst_chain_id: &ChainIdB<Builder>,
        src_client_id: &ClientIdA<Builder>,
        dst_client_id: &ClientIdB<Builder>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Builder>>, Self::Error> {
        <BuildWithCache<BuildRelayFromChains<BuildBatchWorker<BuildRelayFromChainsWithOfa>>>>::build_relay(
            self,
            target,
            src_chain_id,
            dst_chain_id,
            src_client_id,
            dst_client_id,
        )
        .await
    }
}

#[async_trait]
impl<Builder> CanBuildRelay<RelayBToATarget> for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_relay(
        &self,
        target: RelayBToATarget,
        src_chain_id: &ChainIdB<Builder>,
        dst_chain_id: &ChainIdA<Builder>,
        src_client_id: &ClientIdB<Builder>,
        dst_client_id: &ClientIdA<Builder>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Builder>>, Self::Error> {
        <BuildWithCache<BuildRelayFromChains<BuildBatchWorker<BuildRelayFromChainsWithOfa>>>>::build_relay(
            self,
            target,
            src_chain_id,
            dst_chain_id,
            src_client_id,
            dst_client_id,
        )
        .await
    }
}
