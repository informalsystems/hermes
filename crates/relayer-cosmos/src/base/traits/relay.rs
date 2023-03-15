use std::collections::HashSet;

use alloc::sync::Arc;
use futures::lock::Mutex;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use crate::base::traits::chain::CosmosChain;
use crate::base::types::chain::CosmosChainWrapper;

pub trait CosmosRelay: Async {
    type Preset: Async;

    type SrcChain: CosmosChain<Preset = Self::Preset>;

    type DstChain: CosmosChain<Preset = Self::Preset>;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext>;

    fn src_chain(&self) -> &OfaChainWrapper<CosmosChainWrapper<Self::SrcChain>>;

    fn dst_chain(&self) -> &OfaChainWrapper<CosmosChainWrapper<Self::DstChain>>;

    fn src_to_dst_client(
        &self,
    ) -> &ForeignClient<
        <Self::DstChain as CosmosChain>::ChainHandle,
        <Self::SrcChain as CosmosChain>::ChainHandle,
    >;

    fn dst_to_src_client(
        &self,
    ) -> &ForeignClient<
        <Self::SrcChain as CosmosChain>::ChainHandle,
        <Self::DstChain as CosmosChain>::ChainHandle,
    >;

    fn packet_lock_mutex(&self) -> &Arc<Mutex<HashSet<(ChannelId, PortId, ChannelId, PortId)>>>;
}
