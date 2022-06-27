use ibc::core::ics04_channel::packet::Packet;

use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::impls::cosmos::error::Error;
use crate::traits::core::ErrorContext;
use crate::traits::relay_types::RelayTypes;

#[derive(Debug, Clone)]
pub struct CosmosRelayTypes;

impl ErrorContext for CosmosRelayTypes {
    type Error = Error;
}

impl RelayTypes for CosmosRelayTypes {
    type SrcChain = CosmosChainTypes;

    type DstChain = CosmosChainTypes;

    type Packet = Packet;
}
