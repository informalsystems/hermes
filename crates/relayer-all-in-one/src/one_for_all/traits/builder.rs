use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::fmt::Debug;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;

use crate::all_for_one::runtime::AfoRuntime;
use crate::one_for_all::traits::birelay::OfaBiRelay;
use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaBuilder: Async {
    type Error: Debug + Async;

    type Runtime: AfoRuntime;

    type Logger: HasBaseLogLevels;

    type BiRelay: OfaBiRelay;

    fn runtime(&self) -> &Self::Runtime;

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Self::Error;

    fn birelay_error(e: <Self::BiRelay as OfaBiRelay>::Error) -> Self::Error;

    fn logger(&self) -> &Self::Logger;

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

pub type BiRelay<Builder> = <Builder as OfaBuilder>::BiRelay;

pub type RelayAToB<Builder> = <BiRelay<Builder> as OfaBiRelay>::RelayAToB;

pub type RelayBToA<Builder> = <BiRelay<Builder> as OfaBiRelay>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as OfaRelay>::SrcChain;

pub type RelayError<Builder> = <RelayAToB<Builder> as OfaRelay>::Error;

pub type ChainB<Builder> = <RelayAToB<Builder> as OfaRelay>::DstChain;

pub type ChainIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ChainId;

pub type ChainIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ChainId;

pub type ClientIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ClientId;

pub type ClientIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ClientId;

pub type Runtime<Builder> = <Builder as OfaBuilder>::Runtime;

pub type Mutex<Builder, T> = <Runtime<Builder> as HasMutex>::Mutex<T>;

pub type ChainACache<Builder> =
    Arc<Mutex<Builder, BTreeMap<ChainIdA<Builder>, OfaChainWrapper<ChainA<Builder>>>>>;

pub type ChainBCache<Builder> =
    Arc<Mutex<Builder, BTreeMap<ChainIdB<Builder>, OfaChainWrapper<ChainB<Builder>>>>>;

pub type RelayAToBCache<Builder> = Arc<
    Mutex<
        Builder,
        BTreeMap<
            (
                ChainIdA<Builder>,
                ChainIdB<Builder>,
                ClientIdA<Builder>,
                ClientIdB<Builder>,
            ),
            OfaRelayWrapper<RelayAToB<Builder>>,
        >,
    >,
>;

pub type RelayBToACache<Builder> = Arc<
    Mutex<
        Builder,
        BTreeMap<
            (
                ChainIdB<Builder>,
                ChainIdA<Builder>,
                ClientIdB<Builder>,
                ClientIdA<Builder>,
            ),
            OfaRelayWrapper<RelayBToA<Builder>>,
        >,
    >,
>;

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
