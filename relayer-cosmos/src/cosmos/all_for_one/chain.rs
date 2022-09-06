use ibc::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc::core::ics04_channel::events::WriteAcknowledgement;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer_framework::all_for_one::traits::chain::{AfoChainContext, AfoCounterpartyContext};
use ibc_relayer_framework::one_for_all::traits::error::OfaErrorContext;
use ibc_relayer_framework::one_for_all::traits::telemetry::OfaTelemetryWrapper;
use tendermint::abci::responses::Event;

use crate::cosmos::core::error::Error;
use crate::cosmos::core::types::message::CosmosIbcMessage;
use crate::cosmos::core::types::telemetry::CosmosTelemetry;

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
    Telemetry = OfaTelemetryWrapper<CosmosTelemetry>,
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
        Telemetry = OfaTelemetryWrapper<CosmosTelemetry>,
    >,
    Counterparty: AfoCounterpartyContext<Chain>,
{
}
