use ibc_relayer_framework::base::all_for_one::traits::relay::AfoRelayContext;
use ibc_relayer_framework::base::one_for_all::traits::error::OfaErrorContext;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::cosmos::base::all_for_one::chain::AfoCosmosChainWrapper;
use crate::cosmos::base::error::Error;

pub trait AfoCosmosRelayWrapper:
    AfoRelayContext<
    AfoError = OfaErrorContext<Error>,
    AfoSrcChain = Self::CosmosSrcChain,
    AfoDstChain = Self::CosmosDstChain,
    Packet = Packet,
>
{
    type CosmosSrcChain: AfoCosmosChainWrapper<Self::CosmosDstChain>;

    type CosmosDstChain: AfoCosmosChainWrapper<Self::CosmosSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosRelayWrapper for Relay
where
    Relay: AfoRelayContext<
        AfoError = OfaErrorContext<Error>,
        AfoSrcChain = SrcChain,
        AfoDstChain = DstChain,
        Packet = Packet,
    >,
    SrcChain: AfoCosmosChainWrapper<DstChain>,
    DstChain: AfoCosmosChainWrapper<SrcChain>,
{
    type CosmosSrcChain = SrcChain;
    type CosmosDstChain = DstChain;
}
