use core::fmt::Debug;

use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::relay::traits::auto_relayer::AutoRelayer;

use crate::one_for_all::traits::relay::{
    OfaBaseRelay, OfaHomogeneousRelay, OfaRelayPreset, OfaRelayTypes,
};
use crate::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;

pub trait OfaBiRelayTypes: Async {
    type Preset: Async;

    type Error: Debug + Async;

    type Runtime: OfaBaseRuntime;

    type RelayAToB: OfaBaseRelay<Preset = Self::Preset>;

    type RelayBToA: OfaBaseRelay<
        Preset = Self::Preset,
        SrcChain = <Self::RelayAToB as OfaRelayTypes>::DstChain,
        DstChain = <Self::RelayAToB as OfaRelayTypes>::SrcChain,
        Error = <Self::RelayAToB as OfaRelayTypes>::Error,
    >;
}

pub trait OfaBiRelay: OfaBiRelayTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn relay_a_to_b(&self) -> &OfaRelayWrapper<Self::RelayAToB>;

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<Self::RelayBToA>;

    fn relay_error(e: <Self::RelayAToB as OfaRelayTypes>::Error) -> Self::Error;
}

pub trait OfaBiRelayPreset<BiRelay>:
    OfaRelayPreset<BiRelay::RelayAToB> + OfaRelayPreset<BiRelay::RelayBToA>
where
    BiRelay: OfaBiRelayTypes,
{
    type TwoWayAutoRelayer: AutoRelayer<OfaBiRelayWrapper<BiRelay>>;
}

pub trait OfaHomogeneousBiRelay:
    OfaBiRelayTypes<RelayAToB = Self::Relay, RelayBToA = Self::Relay>
{
    type Relay: OfaHomogeneousRelay;
}

impl<BiRelay, Relay> OfaHomogeneousBiRelay for BiRelay
where
    BiRelay: OfaBiRelayTypes<RelayAToB = Relay, RelayBToA = Relay>,
    Relay: OfaHomogeneousRelay,
{
    type Relay = Relay;
}
