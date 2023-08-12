use ibc_relayer_components::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::components::update_client::skip::SkipUpdateClient;
use ibc_relayer_components::relay::components::update_client::wait::WaitUpdateClient;
use ibc_relayer_components::relay::components::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::components::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use ibc_relayer_components::relay::traits::ibc_message_sender::{MainSink, IbcMessageSenderComponent};
use ibc_relayer_components::relay::traits::messages::update_client::UpdateClientMessageBuilderComponent;
use ibc_relayer_components::relay::traits::packet_relayer::PacketRelayerComponent;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::AckPacketRelayerComponent;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayerComponnent;
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayerComponent;

use crate::relayer_mock::base::impls::relay::MockBuildUpdateClientMessage;

pub struct MockComponents;

ibc_relayer_components::forward_component!(
    IbcMessageSenderComponent<MainSink>,
    MockComponents,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

ibc_relayer_components::forward_component!(
    PacketRelayerComponent,
    MockComponents,
    FullCycleRelayer,
);

ibc_relayer_components::forward_component!(
    ReceivePacketRelayerComponnent,
    MockComponents,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

ibc_relayer_components::forward_component!(
    AckPacketRelayerComponent,
    MockComponents,
    BaseAckPacketRelayer,
);

ibc_relayer_components::forward_component!(
    TimeoutUnorderedPacketRelayerComponent,
    MockComponents,
    BaseTimeoutUnorderedPacketRelayer,
);

ibc_relayer_components::forward_component!(
    UpdateClientMessageBuilderComponent,
    MockComponents,
    SkipUpdateClient<WaitUpdateClient<MockBuildUpdateClientMessage>>,
);
