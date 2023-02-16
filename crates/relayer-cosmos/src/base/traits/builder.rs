use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::fmt::Debug;
use ibc_relayer_framework::base::core::traits::sync::Async;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use tokio::sync::Mutex;

use crate::base::traits::birelay::CosmosBiRelay;
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;

pub trait CosmosBuilderTypes: Async {
    type Preset: Async;

    type Error: Debug + Async;

    type BiRelay: CosmosBiRelay<Preset = Self::Preset>;
}

#[async_trait]
pub trait CosmosBuilder: CosmosBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext>;

    fn runtime_error(e: TokioRuntimeError) -> Self::Error;

    fn chain_id_a(&self) -> ChainId;

    fn chain_id_b(&self) -> ChainId;

    fn client_id_a(&self) -> ClientId;

    fn client_id_b(&self) -> ClientId;

    async fn build_chain_a(&self, chain_id: &ChainId) -> Result<ChainA<Self>, Self::Error>;

    async fn build_chain_b(&self, chain_id: &ChainId) -> Result<ChainB<Self>, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Self>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Self>>>,
    ) -> Result<RelayAToB<Self>, Self::Error>;

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Self>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Self>>>,
    ) -> Result<RelayBToA<Self>, Self::Error>;

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<RelayAToB<Self>>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<RelayBToA<Self>>>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

pub type BiRelay<Builder> = <Builder as CosmosBuilderTypes>::BiRelay;

pub type RelayAToB<Builder> = <BiRelay<Builder> as CosmosBiRelay>::RelayAToB;

pub type RelayBToA<Builder> = <BiRelay<Builder> as CosmosBiRelay>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as CosmosRelay>::SrcChain;

pub type ChainB<Builder> = <RelayAToB<Builder> as CosmosRelay>::DstChain;

pub type ChainACache<Builder> =
    Arc<Mutex<BTreeMap<ChainId, OfaChainWrapper<CosmosChainWrapper<ChainA<Builder>>>>>>;

pub type ChainBCache<Builder> =
    Arc<Mutex<BTreeMap<ChainId, OfaChainWrapper<CosmosChainWrapper<ChainB<Builder>>>>>>;

pub type RelayAToBCache<Builder> = Arc<
    Mutex<
        BTreeMap<
            (ChainId, ChainId, ClientId, ClientId),
            OfaRelayWrapper<CosmosRelayWrapper<RelayAToB<Builder>>>,
        >,
    >,
>;

pub type RelayBToACache<Builder> = Arc<
    Mutex<
        BTreeMap<
            (ChainId, ChainId, ClientId, ClientId),
            OfaRelayWrapper<CosmosRelayWrapper<RelayBToA<Builder>>>,
        >,
    >,
>;
