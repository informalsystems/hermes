use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::base::one_for_all::impls::relay::message_builders::update_client::BuildUpdateClientMessageFromOfa;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::chain::{OfaChainPreset, OfaIbcChainPreset};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::impls::messages::skip_update_client::SkipUpdateClient;
use crate::base::relay::impls::messages::wait_update_client::WaitUpdateClient;
use crate::base::relay::impls::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullRelayer;
use crate::base::relay::impls::packet_relayers::general::retry::RetryRelayer;
use crate::base::relay::impls::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::relay::impls::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;

pub struct MinimalPreset;

impl<Chain> OfaChainPreset<Chain> for MinimalPreset
where
    Chain: OfaBaseChain,
{
    type ChainStatusQuerier = SendChainStatusQueryToOfa;
}

impl<Chain, Counterparty> OfaIbcChainPreset<Chain, Counterparty> for MinimalPreset
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = SendConsensusStateQueryToOfa;
}

impl<Relay> OfaRelayPreset<Relay> for MinimalPreset
where
    Relay: OfaBaseRelay<Preset = MinimalPreset>,
{
    type PacketRelayer = RetryRelayer<FullRelayer>;

    type ReceivePacketRelayer = SkipReceivedPacketRelayer<BaseReceivePacketRelayer>;

    type AckPacketRelayer = BaseAckPacketRelayer;

    type TimeoutUnorderedPacketRelayer = BaseTimeoutUnorderedPacketRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessageFromOfa>>;

    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
