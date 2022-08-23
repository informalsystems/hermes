use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_framework::impls::messages::wait_update_client::WaitUpdateClient;
use ibc_relayer_framework::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::one_for_all::impls::chain::OfaConsensusStateQuerier;
use ibc_relayer_framework::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use ibc_relayer_framework::one_for_all::impls::status::OfaChainStatusQuerier;
use ibc_relayer_framework::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use ibc_relayer_framework::one_for_all::traits::components::chain::{
    OfaChainComponents, OfaIbcChainComponents,
};
use ibc_relayer_framework::one_for_all::traits::components::relay::OfaRelayComponents;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelay;

pub struct CosmosComponents;

impl<Chain> OfaChainComponents<Chain> for CosmosComponents
where
    Chain: OfaChain,
{
    type ChainStatusQuerier = OfaChainStatusQuerier;
}

impl<Chain, Counterparty> OfaIbcChainComponents<Chain, Counterparty> for CosmosComponents
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = OfaConsensusStateQuerier;
}

impl<Relay> OfaRelayComponents<Relay> for CosmosComponents
where
    Relay: OfaRelay<Components = CosmosComponents>,
{
    type PacketRelayer = TopRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
