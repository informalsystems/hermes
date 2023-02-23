use alloc::collections::BTreeMap;

use async_trait::async_trait;
use ibc_relayer_all_in_one::one_for_all::traits::builder::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, Mutex, OfaBuilderTypes, RelayAToB,
    RelayBToA, RelayError,
};
use ibc_relayer_all_in_one::one_for_all::traits::runtime::OfaBaseRuntime;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;

use crate::one_for_all::traits::birelay::OfaFullBiRelay;
use crate::one_for_all::traits::runtime::OfaFullRuntime;
use crate::one_for_all::types::batch::aliases::MessageBatchSender;
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

    fn batch_config(&self) -> &BatchConfig;

    async fn build_chain_a(&self, chain_id: &ChainIdA<Self>) -> Result<ChainA<Self>, Self::Error>;

    async fn build_chain_b(&self, chain_id: &ChainIdB<Self>) -> Result<ChainB<Self>, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientIdA<Self>,
        dst_client_id: &ClientIdB<Self>,
        src_chain: OfaChainWrapper<ChainA<Self>>,
        dst_chain: OfaChainWrapper<ChainB<Self>>,
        src_batch_sender: MessageBatchSender<ChainA<Self>, RelayError<Self>>,
        dst_batch_sender: MessageBatchSender<ChainB<Self>, RelayError<Self>>,
    ) -> Result<RelayAToB<Self>, Self::Error>;

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientIdB<Self>,
        dst_client_id: &ClientIdA<Self>,
        src_chain: OfaChainWrapper<ChainB<Self>>,
        dst_chain: OfaChainWrapper<ChainA<Self>>,
        src_batch_sender: MessageBatchSender<ChainB<Self>, RelayError<Self>>,
        dst_batch_sender: MessageBatchSender<ChainA<Self>, RelayError<Self>>,
    ) -> Result<RelayBToA<Self>, Self::Error>;

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Self>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Self>>,
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

pub type BatchSenderCacheA<Build> = Mutex<
    Build,
    BTreeMap<
        (
            ChainIdA<Build>,
            ChainIdB<Build>,
            ClientIdA<Build>,
            ClientIdB<Build>,
        ),
        MessageBatchSender<ChainA<Build>, RelayError<Build>>,
    >,
>;

pub type BatchSenderCacheB<Build> = Mutex<
    Build,
    BTreeMap<
        (
            ChainIdB<Build>,
            ChainIdA<Build>,
            ClientIdB<Build>,
            ClientIdA<Build>,
        ),
        MessageBatchSender<ChainB<Build>, RelayError<Build>>,
    >,
>;
