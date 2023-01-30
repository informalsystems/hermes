use crate::base::chain::traits::types::chain::HasChainTypes;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::types::HasRelayTypes;

pub fn relay_context<Relay: OfaBaseRelay>(relay: Relay) -> impl HasRelayTypes {
    OfaRelayWrapper::new(relay)
}

pub fn chain_context<Chain: OfaBaseChain>(chain: Chain) -> impl HasChainTypes {
    OfaChainWrapper::new(chain)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    chain: Chain,
) -> impl HasIbcChainTypes<OfaChainWrapper<Counterparty>>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    OfaChainWrapper::new(chain)
}
