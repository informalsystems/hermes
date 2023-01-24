use crate::base::one_for_all::presets::min as preset;
use crate::base::one_for_all::presets::min::MinimalPreset;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::chain::{OfaChainPreset, OfaIbcChainPreset};
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset};

impl<Chain> OfaChainPreset<Chain> for MinimalPreset
where
    Chain: OfaBaseChain,
{
    type ChainStatusQuerier = preset::ChainStatusQuerier;
}

impl<Chain, Counterparty> OfaIbcChainPreset<Chain, Counterparty> for MinimalPreset
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type ConsensusStateQuerier = preset::ConsensusStateQuerier;
}

impl<Relay> OfaRelayPreset<Relay> for MinimalPreset
where
    Relay: OfaBaseRelay<Preset = MinimalPreset>,
{
    type AutoRelayer = preset::AutoRelayer;

    type PacketRelayer = preset::PacketRelayer;

    type PacketFilter = preset::PacketFilter;

    type IbcMessageSender = preset::IbcMessageSender;
}
