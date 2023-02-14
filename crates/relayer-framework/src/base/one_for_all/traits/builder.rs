use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::fmt::Debug;

use crate::base::core::traits::sync::Async;
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

    type BiRelay: OfaBiRelay<Preset = Self::Preset>;
}

#[async_trait]
pub trait OfaBuilder: OfaBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn chain_id_a(&self) -> &ChainIdA<Self>;

    fn chain_id_b(&self) -> &ChainIdB<Self>;

    fn client_id_a(&self) -> &ClientIdA<Self>;

    fn client_id_b(&self) -> &ClientIdB<Self>;

    async fn build_chain_a(&self) -> Result<ChainA<Self>, Self::Error>;

    async fn build_chain_b(&self) -> Result<ChainB<Self>, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_chain: OfaChainWrapper<ChainA<Self>>,
        dst_chain: OfaChainWrapper<ChainB<Self>>,
    ) -> Result<RelayAToB<Self>, Self::Error>;

    async fn build_relay_b_to_a(
        &self,
        src_chain: OfaChainWrapper<ChainB<Self>>,
        dst_chain: OfaChainWrapper<ChainA<Self>>,
    ) -> Result<RelayBToA<Self>, Self::Error>;

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Self>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Self>>,
    ) -> Result<Self::BiRelay, Self::Error>;

    fn chain_a_cache(&self) -> &ChainACache<Self>;

    fn chain_b_cache(&self) -> &ChainACache<Self>;

    fn relay_a_to_b_cache(&self) -> &RelayAToBCache<Self>;

    fn relay_b_to_a_cache(&self) -> &RelayBToACache<Self>;
}

pub type BiRelay<Builder> = <Builder as OfaBuilderTypes>::BiRelay;

pub type RelayAToB<Builder> = <BiRelay<Builder> as OfaBiRelayTypes>::RelayAToB;

pub type RelayBToA<Builder> = <BiRelay<Builder> as OfaBiRelayTypes>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::SrcChain;

pub type ChainB<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::DstChain;

pub type ChainIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ChainId;

pub type ChainIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ChainId;

pub type ClientIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ClientId;

pub type ClientIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ClientId;

pub type Runtime<Builder> = <Builder as OfaBuilderTypes>::Runtime;

pub type Mutex<Builder, T> = <Runtime<Builder> as OfaBaseRuntime>::Mutex<T>;

pub type ChainACache<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdA<Builder>, ChainA<Builder>>>>;

pub type ChainBCache<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdB<Builder>, ChainB<Builder>>>>;

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
            RelayAToB<Builder>,
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
            RelayBToA<Builder>,
        >,
    >,
>;
