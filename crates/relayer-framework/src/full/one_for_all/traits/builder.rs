use async_trait::async_trait;

use crate::base::one_for_all::traits::builder::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, OfaBuilderTypes, RelayAToB, RelayBToA,
};
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::full::one_for_all::traits::birelay::OfaFullBiRelay;
use crate::full::one_for_all::traits::runtime::OfaFullRuntime;
use crate::full::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::std_prelude::*;

pub trait OfaFullBuilderTypes:
    OfaBuilderTypes<Runtime = Self::FullRuntime, BiRelay = Self::FullBiRelay>
{
    type FullRuntime: OfaFullRuntime;

    type FullBiRelay: OfaFullBiRelay<Preset = Self::Preset>;
}

#[async_trait]
pub trait OfaFullBuilder: OfaFullBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    async fn build_chain_a(&self, chain_id: &ChainIdA<Self>) -> Result<ChainA<Self>, Self::Error>;

    async fn build_chain_b(&self, chain_id: &ChainIdB<Self>) -> Result<ChainB<Self>, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientIdA<Self>,
        dst_client_id: &ClientIdB<Self>,
        src_chain: OfaChainWrapper<ChainA<Self>>,
        dst_chain: OfaChainWrapper<ChainB<Self>>,
        src_batch_sender: MessageBatchSender<ChainA<Self>, Self::Error>,
        dst_batch_sender: MessageBatchSender<ChainB<Self>, Self::Error>,
    ) -> Result<RelayAToB<Self>, Self::Error>;

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Self>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Self>>,
        src_batch_sender: MessageBatchSender<ChainB<Self>, Self::Error>,
        dst_batch_sender: MessageBatchSender<ChainA<Self>, Self::Error>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

impl<Build> OfaFullBuilderTypes for Build
where
    Build: OfaBuilderTypes,
    Build::Runtime: OfaFullRuntime,
    Build::BiRelay: OfaFullBiRelay,
{
    type FullRuntime = Build::Runtime;

    type FullBiRelay = Build::BiRelay;
}
