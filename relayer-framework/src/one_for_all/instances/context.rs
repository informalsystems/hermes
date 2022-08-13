use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::relay::RelayContext;

pub fn relay_context<Relay: OfaRelay>(
    relay: Relay,
    src_chain: Relay::SrcChain,
    dst_chain: Relay::DstChain,
    runtime: Relay::Runtime,
) -> impl RelayContext {
    OfaRelayContext::new(relay, src_chain, dst_chain, runtime)
}

pub fn chain_context<Chain: OfaChain>(chain: Chain, runtime: Chain::Runtime) -> impl ChainContext {
    OfaChainContext::new(chain, runtime)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    chain: Chain,
    runtime: Chain::Runtime,
) -> impl IbcChainContext<Counterparty>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    OfaChainContext::new(chain, runtime)
}
