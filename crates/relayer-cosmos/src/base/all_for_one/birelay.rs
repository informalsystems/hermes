use ibc_relayer_framework::base::all_for_one::birelay::AfoBaseBiRelay;
use ibc_relayer_framework::base::relay::types::aliases::{DstChain, SrcChain};

use crate::base::all_for_one::relay::AfoCosmosBaseRelay;

pub trait AfoCosmosBaseBiRelay:
    AfoBaseBiRelay<AfoRelayAToB = Self::CosmosRelayAToB, AfoRelayBToA = Self::CosmosRelayBToA>
{
    type CosmosRelayAToB: AfoCosmosBaseRelay;

    type CosmosRelayBToA: AfoCosmosBaseRelay<
        CosmosSrcChain = DstChain<Self::CosmosRelayAToB>,
        CosmosDstChain = SrcChain<Self::CosmosRelayAToB>,
    >;
}
