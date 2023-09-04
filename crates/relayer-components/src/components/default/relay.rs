use core::marker::PhantomData;

use crate::relay::components::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer;
use crate::relay::components::auto_relayers::concurrent_event::ConcurrentEventSubscriptionRelayer;
use crate::relay::components::create_client::CreateClientWithChains;
use crate::relay::components::event_relayers::packet_event::PacketEventRelayer;
use crate::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::relay::components::packet_clearers::receive_packet::ClearReceivePackets;
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
use crate::relay::traits::components::auto_relayer::AutoRelayerComponent;
use crate::relay::traits::components::client_creator::ClientCreatorComponent;
use crate::relay::traits::components::event_relayer::EventRelayerComponent;
use crate::relay::traits::components::ibc_message_sender::{IbcMessageSenderComponent, MainSink};
use crate::relay::traits::components::packet_clearer::PacketClearerComponent;
use crate::relay::traits::components::packet_filter::PacketFilterComponent;
use crate::relay::traits::components::packet_relayer::PacketRelayerComponent;
use crate::relay::traits::components::packet_relayers::ack_packet::AckPacketRelayerComponent;
use crate::relay::traits::components::packet_relayers::receive_packet::ReceivePacketRelayerComponnent;
use crate::relay::traits::components::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayerComponent;
use crate::relay::traits::components::update_client_message_builder::UpdateClientMessageBuilderComponent;

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
    EventRelayerComponent,
    DefaultRelayComponents<BaseComponents>,
    PacketEventRelayer,
);

crate::delegate_component!(
    AutoRelayerComponent,
    DefaultRelayComponents<BaseComponents>,
    ConcurrentBidirectionalRelayer<ConcurrentEventSubscriptionRelayer>,
);

crate::delegate_component!(
    ClientCreatorComponent,
    DefaultRelayComponents<BaseComponents>,
    CreateClientWithChains,
);

crate::delegate_component!(
    PacketClearerComponent,
    DefaultRelayComponents<BaseComponents>,
    ClearReceivePackets,
);
