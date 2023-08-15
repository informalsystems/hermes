use core::marker::PhantomData;

use crate::relay::components::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer;
use crate::relay::components::auto_relayers::concurrent_event::ConcurrentEventSubscriptionRelayer;
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
use crate::relay::traits::auto_relayer::AutoRelayerComponent;
use crate::relay::traits::ibc_message_sender::{IbcMessageSenderComponent, MainSink};
use crate::relay::traits::messages::update_client::UpdateClientMessageBuilderComponent;
use crate::relay::traits::packet_filter::PacketFilterComponent;
use crate::relay::traits::packet_relayer::PacketRelayerComponent;
use crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayerComponent;
use crate::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayerComponnent;
use crate::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayerComponent;

pub struct DefaultRelayComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    IbcMessageSenderComponent<MainSink>,
    DefaultRelayComponents<BaseComponents>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

crate::delegate_component!(
    UpdateClientMessageBuilderComponent,
    DefaultRelayComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

crate::delegate_component!(
    PacketRelayerComponent,
    DefaultRelayComponents<BaseComponents>,
    LockPacketRelayer<LoggerRelayer<FilterRelayer<FullCycleRelayer>>>,
);

crate::delegate_component!(
    PacketFilterComponent,
    DefaultRelayComponents<BaseComponents>,
    BaseComponents,
);

crate::delegate_component!(
    ReceivePacketRelayerComponnent,
    DefaultRelayComponents<BaseComponents>,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

crate::delegate_component!(
    AckPacketRelayerComponent,
    DefaultRelayComponents<BaseComponents>,
    BaseAckPacketRelayer,
);

crate::delegate_component!(
    TimeoutUnorderedPacketRelayerComponent,
    DefaultRelayComponents<BaseComponents>,
    BaseTimeoutUnorderedPacketRelayer,
);

crate::delegate_component!(
    AutoRelayerComponent,
    DefaultRelayComponents<BaseComponents>,
    ConcurrentBidirectionalRelayer<ConcurrentEventSubscriptionRelayer>,
);
