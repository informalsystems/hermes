use ibc_relayer_framework::base::all_for_one::relay::AfoBaseRelay;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::all_for_one::chain::AfoCosmosBaseChain;

pub trait AfoCosmosBaseRelay:
    AfoBaseRelay<
    AfoSrcChain = Self::CosmosSrcChain,
    AfoDstChain = Self::CosmosDstChain,
    AfoBaseRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
>
{
    type CosmosSrcChain: AfoCosmosBaseChain<Self::CosmosDstChain>;

    type CosmosDstChain: AfoCosmosBaseChain<Self::CosmosSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosBaseRelay for Relay
where
    Relay: AfoBaseRelay<
        AfoSrcChain = SrcChain,
        AfoDstChain = DstChain,
        AfoBaseRuntime = OfaRuntimeWrapper<TokioRuntimeContext>,
    >,
    SrcChain: AfoCosmosBaseChain<DstChain>,
    DstChain: AfoCosmosBaseChain<SrcChain>,
{
    type CosmosSrcChain = SrcChain;
    type CosmosDstChain = DstChain;
}
