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
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

pub trait OfaBuilderTypes: Async {
    type Preset: Async;

    type Error: Debug + Async;

    type Runtime: OfaBaseRuntime;

    type BiRelay: OfaBiRelay<Preset = Self::Preset>;
}

pub type BiRelay<Builder> = <Builder as OfaBuilderTypes>::BiRelay;

pub type RelayAToB<Builder> = <BiRelay<Builder> as OfaBiRelayTypes>::RelayAToB;

pub type RelayBToA<Builder> = <BiRelay<Builder> as OfaBiRelayTypes>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::SrcChain;

pub type ChainB<Builder> = <RelayAToB<Builder> as OfaRelayTypes>::DstChain;

pub type ChainIdA<Builder> = <ChainA<Builder> as OfaChainTypes>::ChainId;

pub type ChainIdB<Builder> = <ChainB<Builder> as OfaChainTypes>::ChainId;

pub type Runtime<Builder> = <Builder as OfaBuilderTypes>::Runtime;

pub type Mutex<Builder, T> = <Runtime<Builder> as OfaBaseRuntime>::Mutex<T>;

pub type ChainCacheA<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdA<Builder>, ChainA<Builder>>>>;

pub type ChainCacheB<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdB<Builder>, ChainB<Builder>>>>;

pub type RelayCacheAToB<Builder> =
    Arc<Mutex<Builder, BTreeMap<(ChainIdA<Builder>, ChainIdB<Builder>), RelayAToB<Builder>>>>;

pub type RelayCacheBToA<Builder> =
    Arc<Mutex<Builder, BTreeMap<(ChainIdB<Builder>, ChainIdA<Builder>), RelayBToA<Builder>>>>;

#[async_trait]
pub trait OfaBuilder: OfaBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn chain_id_a(&self) -> &ChainIdA<Self>;

    fn chain_id_b(&self) -> &ChainIdB<Self>;

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
}
