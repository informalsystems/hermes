use core::fmt::Debug;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset, OfaRelayTypes};
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::relay::traits::auto_relayer::AutoRelayer;

use super::runtime::OfaBaseRuntime;

pub trait OfaBiRelayTypes: Async {
    type Preset: OfaBiRelayPreset<Self>;

    type Error: Debug + Async;

    type Runtime: OfaBaseRuntime;

    type RelayAToB: OfaBaseRelay<Preset = Self::Preset>;

    type RelayBToA: OfaBaseRelay<
        Preset = Self::Preset,
        SrcChain = <Self::RelayAToB as OfaRelayTypes>::DstChain,
        DstChain = <Self::RelayAToB as OfaRelayTypes>::SrcChain,
    >;
}

pub trait OfaBiRelay: OfaBiRelayTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn relay_a_to_b(&self) -> &OfaRelayWrapper<Self::RelayAToB>;

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<Self::RelayBToA>;

    fn error_a_to_b(e: <Self::RelayAToB as OfaRelayTypes>::Error) -> Self::Error;

    fn error_b_to_a(e: <Self::RelayAToB as OfaRelayTypes>::Error) -> Self::Error;
}

pub trait OfaBiRelayPreset<BiRelay>:
    OfaRelayPreset<BiRelay::RelayAToB> + OfaRelayPreset<BiRelay::RelayBToA>
where
    BiRelay: OfaBiRelayTypes,
{
    type TwoWayAutoRelayer: AutoRelayer<OfaBiRelayWrapper<BiRelay>>;
}
