use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::base::one_for_all::impls::relay::message_builders::timeout_unordered_packet::BuildTimeoutUnorderedPacketMessageFromOfa;
use crate::base::one_for_all::impls::relay::message_builders::update_client::BuildUpdateClientMessageFromOfa;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::traits::chain::{OfaChainPreset, OfaIbcChainPreset};
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::impls::messages::skip_update_client::SkipUpdateClient;
use crate::base::relay::impls::messages::wait_update_client::WaitUpdateClient;
use crate::base::relay::impls::packet_relayers::timeout_unordered::wait_timeout::WaitTimeoutUnorderedPacketMessageBuilder;
use crate::common::one_for_all::presets::FullPreset;
use crate::full::batch::message_sender::SendMessagetoBatchWorker;
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::full::one_for_all::traits::components::batch::OfaBatchPreset;
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::full::telemetry::impls::consensus_state::ConsensusStateTelemetryQuerier;
use crate::full::telemetry::impls::status::ChainStatusTelemetryQuerier;

impl<Chain> OfaChainPreset<Chain> for FullPreset
where
    Chain: OfaFullChain,
{
    type ChainStatusQuerier = ChainStatusTelemetryQuerier<SendChainStatusQueryToOfa>;
}

impl<Chain, Counterparty> OfaIbcChainPreset<Chain, Counterparty> for FullPreset
where
    Chain: OfaFullChain,
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = ConsensusStateTelemetryQuerier<SendConsensusStateQueryToOfa>;
}

impl<Relay> OfaRelayPreset<Relay> for FullPreset
where
    Relay: OfaFullRelay<Preset = FullPreset>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessageFromOfa>>;

    type TimeoutUnorderedPacketMessageBuilder =
        WaitTimeoutUnorderedPacketMessageBuilder<BuildTimeoutUnorderedPacketMessageFromOfa>;

    type IbcMessageSender = SendMessagetoBatchWorker;
}

impl<Relay> OfaBatchPreset<Relay> for FullPreset
where
    Relay: OfaFullRelay<Preset = FullPreset>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type IbcMessageSenderForBatchWorker = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
