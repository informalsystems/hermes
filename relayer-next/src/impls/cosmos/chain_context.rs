use core::fmt::Debug;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::traits::chain_context::{ChainContext, IbcChainContext};

#[derive(Debug, Clone)]
pub struct CosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
}

impl<Handle: ChainHandle> ChainContext for CosmosChainContext<Handle> {
    type Error = Error;

    type Height = Height;
    type Timestamp = Timestamp;
    type Message = CosmosIbcMessage;
}

impl<Chain, Counterparty> IbcChainContext<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    type ChannelId = ChannelId;
    type PortId = PortId;
    type Sequence = Sequence;

    type IbcMessage = CosmosIbcMessage;
    type IbcEvent = IbcEvent;
}
