use crate::base::one_for_all::impls::chain::OfaConsensusStateQuerier;
use crate::base::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use crate::base::one_for_all::impls::status::OfaBaseChainStatusQuerier;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::traits::components::chain::{
    OfaBaseChainComponents, OfaIbcChainComponents,
};
use crate::base::one_for_all::traits::components::relay::OfaBaseRelayComponents;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::impls::messages::skip_update_client::SkipUpdateClient;
use crate::base::relay::impls::messages::wait_update_client::WaitUpdateClient;
use crate::base::relay::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use crate::base::relay::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::relay::impls::packet_relayers::full_relay::FullRelayer;
use crate::base::relay::impls::packet_relayers::retry::RetryRelayer;
use crate::base::relay::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::relay::impls::packet_relayers::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use crate::full::batch::message_sender::SendMessagetoBatchWorker;
use crate::full::filter::impls::filter_relayer::FilterRelayer;
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::full::one_for_all::traits::components::batch::OfaBatchComponents;
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::full::telemetry::impls::consensus_state::ConsensusStateTelemetryQuerier;
use crate::full::telemetry::impls::status::ChainStatusTelemetryQuerier;

pub struct FullComponents;

impl<Chain> OfaBaseChainComponents<Chain> for FullComponents
where
    Chain: OfaFullChain,
{
    type ChainStatusQuerier = ChainStatusTelemetryQuerier<OfaBaseChainStatusQuerier>;
}

impl<Chain, Counterparty> OfaIbcChainComponents<Chain, Counterparty> for FullComponents
where
    Chain: OfaFullChain,
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = ConsensusStateTelemetryQuerier<OfaConsensusStateQuerier>;
}

impl<Relay> OfaBaseRelayComponents<Relay> for FullComponents
where
    Relay: OfaFullRelay<Components = FullComponents>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type PacketRelayer = FilterRelayer<RetryRelayer<FullRelayer>>;

    type ReceivePacketRelayer = SkipReceivedPacketRelayer<BaseReceivePacketRelayer>;

    type AckPacketRelayer = BaseAckPacketRelayer;

    type TimeoutUnorderedPacketRelayer = BaseTimeoutUnorderedPacketRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type IbcMessageSender = SendMessagetoBatchWorker;
}

impl<Relay> OfaBatchComponents<Relay> for FullComponents
where
    Relay: OfaFullRelay<Components = FullComponents>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type IbcMessageSenderForBatchWorker = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
