use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::base::one_for_all::presets::MinimalPreset;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::chain::{OfaChainPreset, OfaIbcChainPreset};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullRelayer;
use crate::base::relay::impls::packet_relayers::general::retry::RetryRelayer;

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

    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
