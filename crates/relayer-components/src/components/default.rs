use core::marker::PhantomData;

use crate::relay::components::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer;
use crate::relay::components::auto_relayers::concurrent_event::ConcurrentEventSubscriptionRelayer;
use crate::relay::components::auto_relayers::concurrent_two_way::ConcurrentTwoWayAutoRelay;
use crate::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::relay::components::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use crate::relay::components::packet_relayers::general::filter_relayer::FilterRelayer;
use crate::relay::components::packet_relayers::general::full_relay::FullCycleRelayer;
use crate::relay::components::packet_relayers::general::lock::LockPacketRelayer;
use crate::relay::components::packet_relayers::general::log::LoggerRelayer;
use crate::relay::components::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use crate::relay::components::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use crate::relay::components::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use crate::relay::components::update_client::build::BuildUpdateClientMessages;
use crate::relay::components::update_client::skip::SkipUpdateClient;
use crate::relay::components::update_client::wait::WaitUpdateClient;
use crate::relay::traits::auto_relayer::{BiRelayMode, RelayMode};
use crate::relay::traits::ibc_message_sender::{ForwardIbcMessageSender, MainSink};
use crate::relay::traits::packet_relayer::ForwardPacketRelayer;
use crate::std_prelude::*;

pub struct DefaultComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::derive_chain_status_querier!(DefaultComponents<BaseComponents>, BaseComponents);

crate::derive_consensus_state_querier!(DefaultComponents<BaseComponents>, BaseComponents);

crate::forward_component!(
    ForwardIbcMessageSender<MainSink>,
    DefaultComponents<BaseComponents>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

crate::derive_update_client_message_builder!(
    DefaultComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

crate::forward_component!(
    ForwardPacketRelayer,
    DefaultComponents<BaseComponents>,
    LockPacketRelayer<LoggerRelayer<FilterRelayer<FullCycleRelayer>>>,
);

crate::derive_packet_filter!(DefaultComponents<BaseComponents>, BaseComponents);

crate::derive_receive_packet_relayer!(
    DefaultComponents<BaseComponents>,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

crate::derive_ack_packet_relayer!(DefaultComponents<BaseComponents>, BaseAckPacketRelayer,);

crate::derive_timeout_unordered_packet_relayer!(
    DefaultComponents<BaseComponents>,
    BaseTimeoutUnorderedPacketRelayer,
);

crate::derive_auto_relayer!(
    RelayMode,
    DefaultComponents<BaseComponents>,
    ConcurrentBidirectionalRelayer<ConcurrentEventSubscriptionRelayer>,
);

crate::derive_auto_relayer!(
    BiRelayMode,
    DefaultComponents<BaseComponents>,
    ConcurrentTwoWayAutoRelay,
);
