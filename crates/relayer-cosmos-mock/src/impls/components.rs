use ibc_relayer_components::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::components::update_client::skip::SkipUpdateClient;
use ibc_relayer_components::relay::components::update_client::wait::WaitUpdateClient;
use ibc_relayer_components::relay::components::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use ibc_relayer_components::relay::traits::ibc_message_sender::{MainSink, IbcMessageSenderComponent};
use ibc_relayer_components::relay::traits::update_client::UpdateClientMessageBuilderComponent;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::AckPacketRelayerComponent;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayerComponnent;
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayerComponent;

use crate::impls::relay::MockCosmosBuildUpdateClientMessage;

pub struct MockCosmosComponents;

ibc_relayer_components::delegate_component!(
    IbcMessageSenderComponent<MainSink>,
    MockCosmosComponents,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

ibc_relayer_components::delegate_component!(
    ReceivePacketRelayerComponnent,
    MockCosmosComponents,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

ibc_relayer_components::delegate_component!(
    AckPacketRelayerComponent,
    MockCosmosComponents,
    BaseAckPacketRelayer,
);

ibc_relayer_components::delegate_component!(
    TimeoutUnorderedPacketRelayerComponent,
    MockCosmosComponents,
    BaseTimeoutUnorderedPacketRelayer,
);

ibc_relayer_components::delegate_component!(
    UpdateClientMessageBuilderComponent,
    MockCosmosComponents,
    SkipUpdateClient<WaitUpdateClient<MockCosmosBuildUpdateClientMessage>>,
);
