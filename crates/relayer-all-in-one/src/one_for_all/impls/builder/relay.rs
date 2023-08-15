use async_trait::async_trait;
use ibc_relayer_components::builder::impls::cache::BuildRelayWithCache;
use ibc_relayer_components::builder::impls::relay::BuildRelayFromChains;
use ibc_relayer_components::builder::traits::relay::{CanBuildRelay, RelayBuilder};
use ibc_relayer_components::builder::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use ibc_relayer_components_extra::builder::impls::batch::BuildBatchWorker;
use ibc_relayer_components_extra::builder::traits::relay::RelayBuilderWithBatch;

use crate::one_for_all::traits::builder::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, OfaBuilder, RelayAToB, RelayBToA,
    RelayError,
};
use crate::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

pub struct BuildRelayFromChainsWithOfa;

#[async_trait]
impl<Build> RelayBuilderWithBatch<OfaBuilderWrapper<Build>, RelayAToBTarget>
    for BuildRelayFromChainsWithOfa
where
    Build: OfaBuilder,
{
    async fn build_relay_with_batch(
        build: &OfaBuilderWrapper<Build>,
        _target: RelayAToBTarget,
        src_client_id: &ClientIdA<Build>,
        dst_client_id: &ClientIdB<Build>,
        src_chain: OfaChainWrapper<ChainA<Build>>,
        dst_chain: OfaChainWrapper<ChainB<Build>>,
        src_batch_sender: MessageBatchSender<ChainA<Build>, RelayError<Build>>,
        dst_batch_sender: MessageBatchSender<ChainB<Build>, RelayError<Build>>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Build>>, Build::Error> {
        let relay_a_to_b = OfaBuilder::build_relay_a_to_b(
            build.builder.as_ref(),
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
        .await?;

        Ok(OfaRelayWrapper::new(relay_a_to_b))
    }
}

#[async_trait]
impl<Build> RelayBuilderWithBatch<OfaBuilderWrapper<Build>, RelayBToATarget>
    for BuildRelayFromChainsWithOfa
where
    Build: OfaBuilder,
{
    async fn build_relay_with_batch(
        build: &OfaBuilderWrapper<Build>,
        _target: RelayBToATarget,
        src_client_id: &ClientIdB<Build>,
        dst_client_id: &ClientIdA<Build>,
        src_chain: OfaChainWrapper<ChainB<Build>>,
        dst_chain: OfaChainWrapper<ChainA<Build>>,
        src_batch_sender: MessageBatchSender<ChainB<Build>, RelayError<Build>>,
        dst_batch_sender: MessageBatchSender<ChainA<Build>, RelayError<Build>>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Build>>, Build::Error> {
        let relay_b_to_a = OfaBuilder::build_relay_b_to_a(
            build.builder.as_ref(),
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
        .await?;

        Ok(OfaRelayWrapper::new(relay_b_to_a))
    }
}

#[async_trait]
impl<Builder> CanBuildRelay<RelayAToBTarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    async fn build_relay(
        &self,
        target: RelayAToBTarget,
        src_chain_id: &ChainIdA<Builder>,
        dst_chain_id: &ChainIdB<Builder>,
        src_client_id: &ClientIdA<Builder>,
        dst_client_id: &ClientIdB<Builder>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Builder>>, Self::Error> {
        <BuildRelayWithCache<BuildRelayFromChains<BuildBatchWorker<BuildRelayFromChainsWithOfa>>>>::build_relay(
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
impl<Builder> CanBuildRelay<RelayBToATarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    async fn build_relay(
        &self,
        target: RelayBToATarget,
        src_chain_id: &ChainIdB<Builder>,
        dst_chain_id: &ChainIdA<Builder>,
        src_client_id: &ClientIdB<Builder>,
        dst_client_id: &ClientIdA<Builder>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Builder>>, Self::Error> {
        <BuildRelayWithCache<BuildRelayFromChains<BuildBatchWorker<BuildRelayFromChainsWithOfa>>>>::build_relay(
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
