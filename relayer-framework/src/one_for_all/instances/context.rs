use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::relay_context::RelayContext;

pub fn relay_context<Relay: OfaRelay>(
    relay: Relay,
    src_chain: Relay::SrcChain,
    dst_chain: Relay::DstChain,
    src_client_id: <Relay::SrcChain as OfaChain>::ClientId,
    dst_client_id: <Relay::DstChain as OfaChain>::ClientId,
    runtime: Relay::Runtime,
) -> impl RelayContext {
    OfaRelayContext::new(
        relay,
        src_chain,
        dst_chain,
        src_client_id,
        dst_client_id,
        runtime,
    )
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
