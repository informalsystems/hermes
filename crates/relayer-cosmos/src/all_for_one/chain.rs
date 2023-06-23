use alloc::sync::Arc;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer_all_in_one::all_for_one::chain::{AfoChain, AfoCounterpartyChain};
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use tendermint::abci::Event as AbciEvent;

use crate::types::error::Error;
use crate::types::message::CosmosIbcMessage;

pub trait AfoCosmosChain<Counterparty>:
    AfoChain<
    Counterparty,
    AfoRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
    Error = Error,
    Height = Height,
    Timestamp = Timestamp,
    Message = CosmosIbcMessage,
    Event = Arc<AbciEvent>,
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

impl<Chain, Counterparty> AfoCosmosChain<Counterparty> for Chain
where
    Chain: AfoChain<
        Counterparty,
        AfoRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
        Error = Error,
        Height = Height,
        Timestamp = Timestamp,
        Message = CosmosIbcMessage,
        Event = Arc<AbciEvent>,
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
