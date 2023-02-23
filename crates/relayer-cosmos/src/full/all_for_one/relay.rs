use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::extra::all_for_one::relay::AfoFullRelay;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::full::all_for_one::chain::AfoCosmosFullChain;

pub trait AfoCosmosFullRelay:
    AfoFullRelay<
    AfoSrcFullChain = Self::CosmosSrcChain,
    AfoDstFullChain = Self::CosmosDstChain,
    Packet = Packet,
    AfoBaseRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
>
{
    type CosmosSrcChain: AfoCosmosFullChain<Self::CosmosDstChain>;

    type CosmosDstChain: AfoCosmosFullChain<Self::CosmosSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosFullRelay for Relay
where
    Relay: AfoFullRelay<
        AfoSrcFullChain = SrcChain,
        AfoDstFullChain = DstChain,
        Packet = Packet,
        AfoBaseRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
    >,
    SrcChain: AfoCosmosFullChain<DstChain>,
    DstChain: AfoCosmosFullChain<SrcChain>,
{
    type CosmosSrcChain = SrcChain;
    type CosmosDstChain = DstChain;
}
