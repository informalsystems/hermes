use core::marker::PhantomData;

use ibc_relayer_components::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::components::update_client::build::BuildUpdateClientMessages;
use ibc_relayer_components::relay::components::update_client::skip::SkipUpdateClient;
use ibc_relayer_components::relay::components::update_client::wait::WaitUpdateClient;
use ibc_relayer_components::relay::components::packet_relayers::general::filter_relayer::FilterRelayer;
use ibc_relayer_components::relay::components::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::lock::LockPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::components::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::log::LoggerRelayer;
use ibc_relayer_components::relay::components::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_components::relay::traits::auto_relayer::{RelayMode, BiRelayMode};
use ibc_relayer_components::relay::traits::ibc_message_sender::MainSink;

use crate::batch::components::message_sender::SendMessagesToBatchWorker;
use crate::batch::types::sink::BatchWorkerSink;
use crate::relay::components::auto_relayers::parallel_bidirectional::ParallelBidirectionalRelayer;
use crate::relay::components::auto_relayers::parallel_event::ParallelEventSubscriptionRelayer;
use crate::relay::components::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;
use crate::relay::components::packet_relayers::retry::RetryRelayer;
use crate::std_prelude::*;
use crate::telemetry::components::consensus_state::ConsensusStateTelemetryQuerier;
use crate::telemetry::components::status::ChainStatusTelemetryQuerier;

pub struct ExtraComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::derive_chain_status_querier!(
    ExtraComponents<BaseComponents>,
    ChainStatusTelemetryQuerier<BaseComponents>,
);

ibc_relayer_components::derive_consensus_state_querier!(
    ExtraComponents<BaseComponents>,
    ConsensusStateTelemetryQuerier<BaseComponents>,
);

ibc_relayer_components::derive_ibc_message_sender!(
    MainSink,
    ExtraComponents<BaseComponents>,
    SendMessagesToBatchWorker,
);

ibc_relayer_components::derive_ibc_message_sender!(
    BatchWorkerSink,
    ExtraComponents<BaseComponents>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

ibc_relayer_components::derive_update_client_message_builder!(
    ExtraComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

ibc_relayer_components::derive_packet_relayer!(
    ExtraComponents<BaseComponents>,
    LockPacketRelayer<LoggerRelayer<FilterRelayer<RetryRelayer<FullCycleRelayer>>>>,
);

ibc_relayer_components::derive_packet_filter!(ExtraComponents<BaseComponents>, BaseComponents);

ibc_relayer_components::derive_receive_packet_relayer!(
    ExtraComponents<BaseComponents>,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

ibc_relayer_components::derive_ack_packet_relayer!(
    ExtraComponents<BaseComponents>,
    BaseAckPacketRelayer,
);

ibc_relayer_components::derive_timeout_unordered_packet_relayer!(
    ExtraComponents<BaseComponents>,
    BaseTimeoutUnorderedPacketRelayer,
);

ibc_relayer_components::derive_auto_relayer!(
    RelayMode,
    ExtraComponents<BaseComponents>,
    ParallelBidirectionalRelayer<ParallelEventSubscriptionRelayer>,
);

ibc_relayer_components::derive_auto_relayer!(
    BiRelayMode,
    ExtraComponents<BaseComponents>,
    ParallelTwoWayAutoRelay,
);
