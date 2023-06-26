use std::collections::HashSet;

use alloc::sync::Arc;
use futures::lock::Mutex;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use crate::contexts::chain::CosmosChain;
use crate::types::batch::CosmosBatchSender;

pub struct CosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub src_chain: OfaChainWrapper<CosmosChain<SrcChain>>,
    pub dst_chain: OfaChainWrapper<CosmosChain<DstChain>>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    pub packet_filter: PacketFilter,
    pub packet_lock_mutex: Arc<Mutex<HashSet<(ChannelId, PortId, ChannelId, PortId, Sequence)>>>,
    pub src_chain_message_batch_sender: CosmosBatchSender,
    pub dst_chain_message_batch_sender: CosmosBatchSender,
}

impl<SrcChain, DstChain> CosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new(
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
        src_chain: OfaChainWrapper<CosmosChain<SrcChain>>,
        dst_chain: OfaChainWrapper<CosmosChain<DstChain>>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
        packet_filter: PacketFilter,
        src_chain_message_batch_sender: CosmosBatchSender,
        dst_chain_message_batch_sender: CosmosBatchSender,
    ) -> Self {
        let relay = Self {
            runtime,
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            packet_filter,
            src_chain_message_batch_sender,
            dst_chain_message_batch_sender,
            packet_lock_mutex: Arc::new(Mutex::new(HashSet::new())),
        };

        relay
    }
}
