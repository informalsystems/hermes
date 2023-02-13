use alloc::collections::BTreeMap;
use async_trait::async_trait;
use core::fmt::Debug;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset, OfaRelayTypes};
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::relay::traits::auto_relayer::AutoRelayer;
use crate::std_prelude::*;

pub trait OfaBuilderTypes: Async {
    type Preset: OfaBuilderPreset<Self>;

    type Error: Debug + Async;

    type Runtime: OfaBaseRuntime;

    type ChainA: OfaIbcChain<Self::ChainB, Preset = Self::Preset>;

    type ChainB: OfaIbcChain<
        Self::ChainA,
        Preset = Self::Preset,
        IncomingPacket = <Self::ChainA as OfaIbcChain<Self::ChainB>>::OutgoingPacket,
        OutgoingPacket = <Self::ChainA as OfaIbcChain<Self::ChainB>>::IncomingPacket,
    >;

    type RelayAToB: OfaBaseRelay<
        Preset = Self::Preset,
        SrcChain = Self::ChainA,
        DstChain = Self::ChainB,
    >;

    type RelayBToA: OfaBaseRelay<
        Preset = Self::Preset,
        SrcChain = Self::ChainB,
        DstChain = Self::ChainA,
        Error = <Self::RelayAToB as OfaRelayTypes>::Error,
    >;
}

#[async_trait]
pub trait OfaBuilder: OfaBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn chain_id_a(&self) -> &<Self::ChainA as OfaChainTypes>::ChainId;

    fn chain_id_b(&self) -> &<Self::ChainB as OfaChainTypes>::ChainId;

    fn chain_cache_a(
        &self,
    ) -> &<Self::Runtime as OfaBaseRuntime>::Mutex<
        BTreeMap<<Self::ChainA as OfaChainTypes>::ChainId, OfaChainWrapper<Self::ChainA>>,
    >;

    fn chain_cache_b(
        &self,
    ) -> &<Self::Runtime as OfaBaseRuntime>::Mutex<
        BTreeMap<<Self::ChainB as OfaChainTypes>::ChainId, OfaChainWrapper<Self::ChainB>>,
    >;

    async fn build_chain_a(&self) -> Result<Self::ChainA, Self::Error>;

    async fn build_chain_b(&self) -> Result<Self::ChainB, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_chain: OfaChainWrapper<Self::ChainA>,
        dst_chain: OfaChainWrapper<Self::ChainB>,
    ) -> Result<Self::RelayAToB, Self::Error>;

    async fn build_relay_b_to_a(
        &self,
        src_chain: OfaChainWrapper<Self::ChainB>,
        dst_chain: OfaChainWrapper<Self::ChainA>,
    ) -> Result<Self::RelayBToA, Self::Error>;
}

pub trait OfaBuilderPreset<Builder>:
    OfaRelayPreset<Builder::RelayAToB> + OfaRelayPreset<Builder::RelayBToA>
where
    Builder: OfaBuilderTypes,
{
    type AutoRelayer: AutoRelayer<OfaBuilderWrapper<Builder>>;
}
