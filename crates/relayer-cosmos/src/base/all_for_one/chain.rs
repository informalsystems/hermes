use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer_all_in_one::base::all_for_one::chain::{AfoBaseChain, AfoCounterpartyChain};
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use tendermint::abci::Event;

use crate::base::error::Error;
use crate::base::types::message::CosmosIbcMessage;

pub trait AfoCosmosBaseChain<Counterparty>:
    AfoBaseChain<
    Counterparty,
    AfoBaseRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
    Error = Error,
    Height = Height,
    Timestamp = Timestamp,
    Message = CosmosIbcMessage,
    Event = Event,
    ClientId = ClientId,
    ConnectionId = ConnectionId,
    ChannelId = ChannelId,
    PortId = PortId,
    Sequence = Sequence,
    WriteAcknowledgementEvent = WriteAcknowledgement,
    ConsensusState = ConsensusState,
    ChainStatus = ChainStatus,
    IncomingPacket = Packet,
    OutgoingPacket = Packet,
>
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoCosmosBaseChain<Counterparty> for Chain
where
    Chain: AfoBaseChain<
        Counterparty,
        AfoBaseRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
        Error = Error,
        Height = Height,
        Timestamp = Timestamp,
        Message = CosmosIbcMessage,
        Event = Event,
        ClientId = ClientId,
        ConnectionId = ConnectionId,
        ChannelId = ChannelId,
        PortId = PortId,
        Sequence = Sequence,
        WriteAcknowledgementEvent = WriteAcknowledgement,
        ConsensusState = ConsensusState,
        ChainStatus = ChainStatus,
        IncomingPacket = Packet,
        OutgoingPacket = Packet,
    >,
    Counterparty: AfoCounterpartyChain<Chain>,
{
}
