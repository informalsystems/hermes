use ibc::core::ics04_channel::packet::Packet;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::impls::cosmos::chain_context::CosmosChainContext;
use crate::impls::cosmos::error::Error;
use crate::traits::relay_context::RelayContext;

pub struct CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub source_chain: CosmosChainContext<SrcChain>,
    pub destination_chain: CosmosChainContext<DstChain>,

    pub foreign_client_src_to_dst: ForeignClient<DstChain, SrcChain>,
    pub foreign_client_dst_to_src: ForeignClient<SrcChain, DstChain>,
}

impl<SrcChain, DstChain> RelayContext for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type Error = Error;

    type SrcChain = CosmosChainContext<SrcChain>;

    type DstChain = CosmosChainContext<DstChain>;

    type Packet = Packet;

    fn source_chain(&self) -> &Self::SrcChain {
        &self.source_chain
    }

    fn destination_chain(&self) -> &Self::DstChain {
        &self.destination_chain
    }
}
