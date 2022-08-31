use crate::core::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::core::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::core::impls::messages::skip_update_client::SkipUpdateClient;
use crate::core::impls::messages::wait_update_client::WaitUpdateClient;
use crate::core::impls::packet_relayers::top::TopRelayer;
use crate::core::impls::queries::chain_status_telemetry::ChainStatusTelemetryQuerier;
use crate::one_for_all::impls::chain::OfaConsensusStateQuerier;
use crate::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use crate::one_for_all::impls::status::{OfaChainStatusQuerier};
use crate::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use crate::one_for_all::traits::components::chain::{OfaChainComponents, OfaIbcChainComponents};
use crate::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::one_for_all::traits::relay::OfaRelay;

pub struct DefaultComponents;

impl<Chain> OfaChainComponents<Chain> for DefaultComponents
where
    Chain: OfaChain,
{
    type ChainStatusQuerier = ChainStatusTelemetryQuerier<OfaChainStatusQuerier>;
}

impl<Chain, Counterparty> OfaIbcChainComponents<Chain, Counterparty> for DefaultComponents
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = OfaConsensusStateQuerier;
}

impl<Relay> OfaRelayComponents<Relay> for DefaultComponents
where
    Relay: OfaRelay<Components = DefaultComponents>,
{
    type PacketRelayer = TopRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
