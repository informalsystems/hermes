// use async_trait::async_trait;
// use ibc::clients::ics07_tendermint::consensus_state::ConsensusState;
// use ibc::core::ics04_channel::events::WriteAcknowledgement;
// use ibc::core::ics04_channel::packet::Sequence;
// use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
// use ibc::events::IbcEventType;
// use ibc::signer::Signer;
// use ibc::timestamp::Timestamp;
// use ibc::Height;
// use ibc_proto::google::protobuf::Any;
// use ibc_relayer::chain::cosmos::tx::simple_send_tx;
// use ibc_relayer::chain::endpoint::ChainStatus;
// use ibc_relayer::chain::handle::ChainHandle;
// use ibc_relayer::chain::requests::{
//     IncludeProof, QueryConsensusStateRequest, QueryHeight, QueryUnreceivedPacketsRequest,
// };
// use ibc_relayer::consensus_state::AnyConsensusState;
// use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
// use ibc_relayer_framework::all_for_one::traits::chain::{AfoChainContext, AfoCounterpartyContext};
// use ibc_relayer_framework::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
// use ibc_relayer_framework::one_for_all::traits::error::OfaErrorContext;
// use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;
// use tendermint::abci::responses::Event;

// use crate::cosmos::core::error::Error;
// use crate::cosmos::core::traits::chain::CosmosChain;
// use crate::cosmos::core::types::chain::CosmosChainContext;
// use crate::cosmos::core::types::message::CosmosIbcMessage;
// use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

// pub trait AfoCosmosChainContext<Counterparty>:
//     AfoChainContext<
//         Counterparty,
//         Error = OfaErrorContext<Error>,
//         Height = Height,
//         Timestamp = Timestamp,
//         Message = CosmosIbcMessage,
//     >
// where
//     Counterparty: AfoCounterpartyContext<Self>,
// {
// }
