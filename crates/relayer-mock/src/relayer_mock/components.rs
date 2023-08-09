use ibc_relayer_components::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_components::relay::impls::messages::wait_update_client::WaitUpdateClient;
use ibc_relayer_components::relay::impls::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use ibc_relayer_components::relay::traits::ibc_message_sender::MainSink;

use crate::relayer_mock::base::impls::relay::MockBuildUpdateClientMessage;

pub struct MockComponents;

ibc_relayer_components::derive_ibc_message_sender!(
    MainSink,
    MockComponents,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

ibc_relayer_components::derive_packet_relayer!(MockComponents, FullCycleRelayer,);

ibc_relayer_components::derive_receive_packet_relayer!(
    MockComponents,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

ibc_relayer_components::derive_ack_packet_relayer!(MockComponents, BaseAckPacketRelayer,);

ibc_relayer_components::derive_timeout_unordered_packet_relayer!(
    MockComponents,
    BaseTimeoutUnorderedPacketRelayer,
);

ibc_relayer_components::derive_update_client_message_builder!(
    MockComponents,
    SkipUpdateClient<WaitUpdateClient<MockBuildUpdateClientMessage>>,
);
