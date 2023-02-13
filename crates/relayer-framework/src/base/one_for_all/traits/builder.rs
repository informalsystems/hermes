use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::chain::{OfaIbcChain, OfaIbcChainWithPreset};
use crate::base::one_for_all::traits::relay::OfaBaseRelayWithPreset;
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaBuilder: Async {
    type Error: Async;

    type Runtime: OfaBaseRuntime;

    type ChainA: OfaIbcChainWithPreset<Self::ChainB>;

    type ChainB: OfaIbcChainWithPreset<
        Self::ChainA,
        IncomingPacket = <Self::ChainA as OfaIbcChain<Self::ChainB>>::OutgoingPacket,
        OutgoingPacket = <Self::ChainA as OfaIbcChain<Self::ChainB>>::IncomingPacket,
    >;

    type RelayAToB: OfaBaseRelayWithPreset<SrcChain = Self::ChainA, DstChain = Self::ChainB>;

    type RelayBToA: OfaBaseRelayWithPreset<SrcChain = Self::ChainA, DstChain = Self::ChainB>;

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
