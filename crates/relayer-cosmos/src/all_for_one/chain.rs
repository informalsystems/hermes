use alloc::sync::Arc;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer_all_in_one::all_for_one::chain::{AfoChain, AfoCounterpartyChain};
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use tendermint::abci::Event as AbciEvent;

use crate::traits::message::CosmosMessage;
use crate::types::channel::CosmosInitChannelOptions;
use crate::types::connection::CosmosInitConnectionOptions;
use crate::types::error::Error;

pub trait AfoCosmosChain<Counterparty>:
    AfoChain<
    Counterparty,
    AfoRuntime = TokioRuntimeContext,
    Error = Error,
    Height = Height,
    Timestamp = Timestamp,
    Message = Arc<dyn CosmosMessage>,
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
    InitConnectionOptions = CosmosInitConnectionOptions,
    InitChannelOptions = CosmosInitChannelOptions,
>
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoCosmosChain<Counterparty> for Chain
where
    Chain: AfoChain<
        Counterparty,
        AfoRuntime = TokioRuntimeContext,
        Error = Error,
        Height = Height,
        Timestamp = Timestamp,
        Message = Arc<dyn CosmosMessage>,
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
        InitConnectionOptions = CosmosInitConnectionOptions,
        InitChannelOptions = CosmosInitChannelOptions,
    >,
    Counterparty: AfoCounterpartyChain<Chain>,
{
}
