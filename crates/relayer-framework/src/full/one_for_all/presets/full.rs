use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::base::relay::impls::packet_relayers::general::filter_relayer::FilterRelayer;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use crate::full::batch::impls::message_sender::SendMessagesToBatchWorker;
use crate::full::one_for_all::impls::packet_filter::FilterPacketFromOfa;
use crate::full::relay::impls::auto_relayers::parallel_bidirectional::ParallelBidirectionalRelayer;
use crate::full::relay::impls::auto_relayers::parallel_event::ParallelEventSubscriptionRelayer;
use crate::full::relay::impls::packet_relayers::retry::RetryRelayer;
use crate::full::telemetry::impls::consensus_state::ConsensusStateTelemetryQuerier;
use crate::full::telemetry::impls::status::ChainStatusTelemetryQuerier;

pub struct FullPreset;

pub type ChainStatusQuerier = ChainStatusTelemetryQuerier<SendChainStatusQueryToOfa>;

pub type ConsensusStateQuerier = ConsensusStateTelemetryQuerier<SendConsensusStateQueryToOfa>;

pub type AutoRelayer = ParallelBidirectionalRelayer<ParallelEventSubscriptionRelayer>;

pub type PacketRelayer = FilterRelayer<RetryRelayer<FullCycleRelayer>>;

pub type PacketFilter = FilterPacketFromOfa;

pub type IbcMessageSender = SendMessagesToBatchWorker;
