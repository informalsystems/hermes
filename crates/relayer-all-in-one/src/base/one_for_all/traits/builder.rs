use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::fmt::Debug;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;

use crate::base::one_for_all::traits::birelay::{OfaBiRelay, OfaBiRelayTypes};
use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaRelayTypes;
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

pub trait OfaBuilderTypes: Async {
    type Preset: Async;

    type Error: Debug + Async;

    type Runtime: OfaBaseRuntime;

    type Logger: HasBaseLogLevels;

    type BiRelay: OfaBiRelay<Preset = Self::Preset>;
}

#[async_trait]
pub trait OfaBuilder: OfaBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn logger(&self) -> &Self::Logger;

    async fn build_chain_a(&self, chain_id: &ChainIdA<Self>) -> Result<ChainA<Self>, Self::Error>;

    async fn build_chain_b(&self, chain_id: &ChainIdB<Self>) -> Result<ChainB<Self>, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientIdA<Self>,
        dst_client_id: &ClientIdB<Self>,
        src_chain: OfaChainWrapper<ChainA<Self>>,
        dst_chain: OfaChainWrapper<ChainB<Self>>,
    ) -> Result<RelayAToB<Self>, Self::Error>;

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientIdB<Self>,
        dst_client_id: &ClientIdA<Self>,
        src_chain: OfaChainWrapper<ChainB<Self>>,
        dst_chain: OfaChainWrapper<ChainA<Self>>,
    ) -> Result<RelayBToA<Self>, Self::Error>;

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Self>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Self>>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

pub type BiRelay<Builder> = <Builder as OfaBuilderTypes>::BiRelay;

pub type RelayAToB<Builder> = <BiRelay<Builder> as OfaBiRelayTypes>::RelayAToB;

pub type RelayBToA<Builder> = <BiRelay<Builder> as OfaBiRelayTypes>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::SrcChain;

pub type RelayError<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::Error;

pub type ChainB<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::DstChain;

pub type ChainIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ChainId;

pub type ChainIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ChainId;

pub type ClientIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ClientId;

pub type ClientIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ClientId;

pub type Runtime<Builder> = <Builder as OfaBuilderTypes>::Runtime;

pub type Mutex<Builder, T> = <Runtime<Builder> as OfaBaseRuntime>::Mutex<T>;

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
