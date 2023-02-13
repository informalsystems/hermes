use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset, OfaRelayTypes};
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::auto_relayer::AutoRelayer;

pub trait OfaBiRelayTypes: Async {
    type Preset: OfaBiRelayPreset<Self>;

    type RelayAToB: OfaBaseRelay<Preset = Self::Preset>;

    type RelayBToA: OfaBaseRelay<
        Preset = Self::Preset,
        SrcChain = <Self::RelayAToB as OfaRelayTypes>::DstChain,
        DstChain = <Self::RelayAToB as OfaRelayTypes>::SrcChain,
        Error = <Self::RelayAToB as OfaRelayTypes>::Error,
    >;
}

pub trait OfaBiRelay: OfaBiRelayTypes {
    fn relay_a_to_b(&self) -> &OfaRelayWrapper<Self::RelayAToB>;

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<Self::RelayBToA>;
}

pub trait OfaBiRelayPreset<BiRelay>:
    OfaRelayPreset<BiRelay::RelayAToB> + OfaRelayPreset<BiRelay::RelayBToA>
where
    BiRelay: OfaBiRelayTypes,
{
    type AutoRelayer: AutoRelayer<OfaBiRelayWrapper<BiRelay>>;
}
