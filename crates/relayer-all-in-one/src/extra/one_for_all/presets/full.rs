use ibc_relayer_components::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::impls::packet_relayers::general::filter_relayer::FilterRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::log::LoggerRelayer;
use ibc_relayer_components_extra::batch::impls::message_sender::SendMessagesToBatchWorker;
use ibc_relayer_components_extra::relay::impls::auto_relayers::parallel_bidirectional::ParallelBidirectionalRelayer;
use ibc_relayer_components_extra::relay::impls::auto_relayers::parallel_event::ParallelEventSubscriptionRelayer;
use ibc_relayer_components_extra::relay::impls::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;
use ibc_relayer_components_extra::relay::impls::packet_relayers::retry::RetryRelayer;
use ibc_relayer_components_extra::telemetry::impls::consensus_state::ConsensusStateTelemetryQuerier;
use ibc_relayer_components_extra::telemetry::impls::status::ChainStatusTelemetryQuerier;

use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::extra::one_for_all::impls::packet_filter::FilterPacketFromOfa;

pub struct FullPreset;

pub type ChainStatusQuerier = ChainStatusTelemetryQuerier<SendChainStatusQueryToOfa>;

pub type ConsensusStateQuerier = ConsensusStateTelemetryQuerier<SendConsensusStateQueryToOfa>;

pub type AutoRelayer = ParallelBidirectionalRelayer<ParallelEventSubscriptionRelayer>;

pub type PacketRelayer = LoggerRelayer<FilterRelayer<RetryRelayer<FullCycleRelayer>>>;

pub type PacketFilter = FilterPacketFromOfa;

// pub type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
pub type IbcMessageSender = SendMessagesToBatchWorker;

pub type IbcMessageSenderForBatchWorker = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;

pub type TwoWayAutoRelayer = ParallelTwoWayAutoRelay;
