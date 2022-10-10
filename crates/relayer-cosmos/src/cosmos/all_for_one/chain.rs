use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer_framework::base::all_for_one::traits::chain::{
    AfoChainContext, AfoCounterpartyContext,
};
use ibc_relayer_framework::base::one_for_all::traits::error::OfaErrorContext;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use tendermint::abci::responses::Event;

use crate::cosmos::core::error::Error;
use crate::cosmos::core::types::message::CosmosIbcMessage;

pub trait AfoCosmosChainContext<Counterparty>:
    AfoChainContext<
    Counterparty,
    Error = OfaErrorContext<Error>,
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
    Counterparty: AfoCounterpartyContext<Self>,
{
}

impl<Chain, Counterparty> AfoCosmosChainContext<Counterparty> for Chain
where
    Chain: AfoChainContext<
        Counterparty,
        Error = OfaErrorContext<Error>,
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
    Counterparty: AfoCounterpartyContext<Chain>,
{
}
