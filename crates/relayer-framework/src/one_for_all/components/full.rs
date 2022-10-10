use crate::addons::batch::message_sender::SendMessagetoBatchWorker;
use crate::core::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::core::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::core::impls::messages::skip_update_client::SkipUpdateClient;
use crate::core::impls::messages::wait_update_client::WaitUpdateClient;
use crate::core::impls::packet_relayers::top::TopRelayer;
use crate::core::impls::queries::consensus_state::ConsensusStateTelemetryQuerier;
use crate::core::impls::queries::status::ChainStatusTelemetryQuerier;
use crate::one_for_all::impls::chain::OfaConsensusStateQuerier;
use crate::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use crate::one_for_all::impls::status::OfaChainStatusQuerier;
use crate::one_for_all::traits::chain::{OfaFullChain, OfaIbcChain};
use crate::one_for_all::traits::components::batch::OfaBatchComponents;
use crate::one_for_all::traits::components::chain::{OfaChainComponents, OfaIbcChainComponents};
use crate::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::one_for_all::traits::relay::OfaRelay;

pub struct FullComponents;

impl<Chain> OfaChainComponents<Chain> for FullComponents
where
    Chain: OfaFullChain,
{
    type ChainStatusQuerier = ChainStatusTelemetryQuerier<OfaChainStatusQuerier>;
}

impl<Chain, Counterparty> OfaIbcChainComponents<Chain, Counterparty> for FullComponents
where
    Chain: OfaFullChain,
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = ConsensusStateTelemetryQuerier<OfaConsensusStateQuerier>;
}

impl<Relay> OfaRelayComponents<Relay> for FullComponents
where
    Relay: OfaRelay<Components = FullComponents>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type PacketRelayer = TopRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type IbcMessageSender = SendMessagetoBatchWorker;
}

impl<Relay> OfaBatchComponents<Relay> for FullComponents
where
    Relay: OfaRelay<Components = FullComponents>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type IbcMessageSenderForBatchWorker = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
