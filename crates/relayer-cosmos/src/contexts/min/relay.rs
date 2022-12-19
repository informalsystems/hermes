use crate::base::traits::chain::CosmosChain;
use crate::base::traits::relay::CosmosRelay;

use alloc::sync::Arc;
use ibc_relayer::foreign_client::ForeignClient;

pub struct MinCosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: CosmosChain,
    DstChain: CosmosChain,
{
    pub src_chain: Arc<SrcChain>,
    pub dst_chain: Arc<DstChain>,
    pub src_to_dst_client: ForeignClient<
        <DstChain as CosmosChain>::ChainHandle,
        <SrcChain as CosmosChain>::ChainHandle,
    >,
    pub dst_to_src_client: ForeignClient<
        <SrcChain as CosmosChain>::ChainHandle,
        <DstChain as CosmosChain>::ChainHandle,
    >,
}

impl<SrcChain, DstChain> MinCosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: CosmosChain,
    DstChain: CosmosChain,
{
    pub fn new(
        src_chain: Arc<SrcChain>,
        dst_chain: Arc<DstChain>,
        src_to_dst_client: ForeignClient<
            <DstChain as CosmosChain>::ChainHandle,
            <SrcChain as CosmosChain>::ChainHandle,
        >,
        dst_to_src_client: ForeignClient<
            <SrcChain as CosmosChain>::ChainHandle,
            <DstChain as CosmosChain>::ChainHandle,
        >,
    ) -> Self {
        let relay = Self {
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
        };

        relay
    }
}

impl<SrcChain, DstChain, Preset> CosmosRelay for MinCosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: CosmosChain<Preset = Preset>,
    DstChain: CosmosChain<Preset = Preset>,
{
    type Preset = Preset;

    type SrcChain = SrcChain;

    type DstChain = DstChain;

    fn src_chain(&self) -> &Arc<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &Arc<Self::DstChain> {
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
}
