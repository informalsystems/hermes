use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer_framework::base::all_for_one::chain::{AfoBaseChain, AfoCounterpartyChain};
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use tendermint::abci::responses::Event;

use crate::base::error::Error;
use crate::base::types::message::CosmosIbcMessage;

pub trait AfoCosmosBaseChain<Counterparty>:
    AfoBaseChain<
    Counterparty,
    Error = Error,
    Height = Height,
    Timestamp = Timestamp,
    Message = CosmosIbcMessage,
    Signer = Signer,
    RawMessage = Any,
    Event = Event,
    ClientId = ClientId,
    ConnectionId = ConnectionId,
    ChannelId = ChannelId,
    PortId = PortId,
    Sequence = Sequence,
    WriteAcknowledgementEvent = WriteAcknowledgement,
    ConsensusState = ConsensusState,
    ChainStatus = ChainStatus,
>
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoCosmosBaseChain<Counterparty> for Chain
where
    Chain: AfoBaseChain<
        Counterparty,
        Error = Error,
        Height = Height,
        Timestamp = Timestamp,
        Message = CosmosIbcMessage,
        Signer = Signer,
        RawMessage = Any,
        Event = Event,
        ClientId = ClientId,
        ConnectionId = ConnectionId,
        ChannelId = ChannelId,
        PortId = PortId,
        Sequence = Sequence,
        WriteAcknowledgementEvent = WriteAcknowledgement,
        ConsensusState = ConsensusState,
        ChainStatus = ChainStatus,
    >,
    Counterparty: AfoCounterpartyChain<Chain>,
{
}
