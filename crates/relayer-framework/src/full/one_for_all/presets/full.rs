use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use crate::full::batch::impls::message_sender::SendMessagesToBatchWorker;
use crate::full::filter::impls::filter_relayer::FilterRelayer;
use crate::full::relay::impls::packet_relayers::retry::RetryRelayer;
use crate::full::telemetry::impls::consensus_state::ConsensusStateTelemetryQuerier;
use crate::full::telemetry::impls::status::ChainStatusTelemetryQuerier;

pub struct FullPreset;

pub type ChainStatusQuerier = ChainStatusTelemetryQuerier<SendChainStatusQueryToOfa>;

pub type ConsensusStateQuerier = ConsensusStateTelemetryQuerier<SendConsensusStateQueryToOfa>;

pub type PacketRelayer = FilterRelayer<RetryRelayer<FullCycleRelayer>>;

pub type IbcMessageSender = SendMessagesToBatchWorker;
