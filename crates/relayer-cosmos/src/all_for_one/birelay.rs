use ibc_relayer_all_in_one::all_for_one::birelay::AfoBiRelay;
use ibc_relayer_components::relay::types::aliases::{DstChain, SrcChain};

use crate::all_for_one::relay::AfoCosmosRelay;

pub trait AfoCosmosBiRelay:
    AfoBiRelay<AfoRelayAToB = Self::CosmosRelayAToB, AfoRelayBToA = Self::CosmosRelayBToA>
{
    type CosmosRelayAToB: AfoCosmosRelay;

    type CosmosRelayBToA: AfoCosmosRelay<
        CosmosSrcChain = DstChain<Self::CosmosRelayAToB>,
        CosmosDstChain = SrcChain<Self::CosmosRelayAToB>,
    >;
}

impl<BiRelay, RelayAToB, RelayBToA> AfoCosmosBiRelay for BiRelay
where
    BiRelay: AfoBiRelay<AfoRelayAToB = RelayAToB, AfoRelayBToA = RelayBToA>,
    RelayAToB: AfoCosmosRelay,
    RelayBToA: AfoCosmosRelay<
        CosmosSrcChain = RelayAToB::CosmosDstChain,
        CosmosDstChain = RelayAToB::CosmosSrcChain,
    >,
{
    type CosmosRelayAToB = RelayAToB;

    type CosmosRelayBToA = RelayBToA;
}
