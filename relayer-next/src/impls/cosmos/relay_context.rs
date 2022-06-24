use ibc::core::ics04_channel::packet::Packet;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::chain_context::CosmosChainContext;
use crate::traits::relay_context::RelayContext;
use crate::types::error::Error;

pub struct CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub source_chain: CosmosChainContext<SrcChain>,
    pub destination_chain: CosmosChainContext<DstChain>,
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
