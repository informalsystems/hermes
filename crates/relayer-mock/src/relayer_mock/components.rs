use ibc_relayer_components::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_components::relay::impls::messages::wait_update_client::WaitUpdateClient;
use ibc_relayer_components::relay::impls::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;

use crate::relayer_mock::base::impls::relay::MockBuildUpdateClientMessage;

pub type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;

pub type PacketRelayer = FullCycleRelayer;

pub type AckPacketRelayer = BaseAckPacketRelayer;

pub type ReceivePacketRelayer = SkipReceivedPacketRelayer<BaseReceivePacketRelayer>;

pub type TimeoutUnorderedPacketRelayer = BaseTimeoutUnorderedPacketRelayer;

pub type UpdateClientMessageBuilder =
    SkipUpdateClient<WaitUpdateClient<MockBuildUpdateClientMessage>>;
