use std::collections::HashSet;

use alloc::sync::Arc;
use futures::lock::Mutex;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::base::one_for_all::presets::min::MinimalPreset;
use ibc_relayer_all_in_one::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use crate::base::traits::chain::CosmosChain;
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::contexts::min::chain::MinCosmosChainContext;

pub struct MinCosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub src_chain: OfaChainWrapper<CosmosChainWrapper<MinCosmosChainContext<SrcChain>>>,
    pub dst_chain: OfaChainWrapper<CosmosChainWrapper<MinCosmosChainContext<DstChain>>>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    pub packet_lock_mutex: Arc<Mutex<HashSet<(ChannelId, PortId, ChannelId, PortId, Sequence)>>>,
}

impl<SrcChain, DstChain> MinCosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new(
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
        src_chain: OfaChainWrapper<CosmosChainWrapper<MinCosmosChainContext<SrcChain>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<MinCosmosChainContext<DstChain>>>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    ) -> Self {
        let relay = Self {
            runtime,
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            packet_lock_mutex: Arc::new(Mutex::new(HashSet::new())),
        };

        relay
    }
}

impl<SrcChain, DstChain> CosmosRelay for MinCosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type Preset = MinimalPreset;

    type SrcChain = MinCosmosChainContext<SrcChain>;

    type DstChain = MinCosmosChainContext<DstChain>;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn src_chain(&self) -> &OfaChainWrapper<CosmosChainWrapper<Self::SrcChain>> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &OfaChainWrapper<CosmosChainWrapper<Self::DstChain>> {
        &self.dst_chain
    }

    fn src_to_dst_client(
        &self,
    ) -> &ForeignClient<
        <Self::DstChain as CosmosChain>::ChainHandle,
        <Self::SrcChain as CosmosChain>::ChainHandle,
    > {
        &self.src_to_dst_client
    }

    fn dst_to_src_client(
        &self,
    ) -> &ForeignClient<
        <Self::SrcChain as CosmosChain>::ChainHandle,
        <Self::DstChain as CosmosChain>::ChainHandle,
    > {
        &self.dst_to_src_client
    }

    fn packet_lock_mutex(
        &self,
    ) -> &Arc<Mutex<HashSet<(ChannelId, PortId, ChannelId, PortId, Sequence)>>> {
        &self.packet_lock_mutex
    }
}
