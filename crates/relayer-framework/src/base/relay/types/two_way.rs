use async_trait::async_trait;
use core::fmt::Debug;
use core::marker::PhantomData;

use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::auto_relayer::{AutoRelayer, CanAutoRelay};
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[derive(Clone)]
pub struct TwoWayRelayContext<Relayer, RelayAToB, RelayBToA> {
    pub relay_a_to_b: RelayAToB,
    pub relay_b_to_a: RelayBToA,
    pub phantom: PhantomData<Relayer>,
}

impl<Relayer, RelayAToB, RelayBToA> TwoWayRelayContext<Relayer, RelayAToB, RelayBToA> {
    pub fn new(_relayer: Relayer, relay_a_to_b: RelayAToB, relay_b_to_a: RelayBToA) -> Self {
        Self {
            relay_a_to_b,
            relay_b_to_a,
            phantom: PhantomData,
        }
    }
}

impl<Error, Relayer, RelayAToB, RelayBToA> HasErrorType
    for TwoWayRelayContext<Relayer, RelayAToB, RelayBToA>
where
    Relayer: Async,
    Error: Debug + Async,
    RelayAToB: HasRelayTypes<Error = Error>,
    RelayBToA: HasRelayTypes<Error = Error>,
{
    type Error = Error;
}

impl<Error, Relayer, RelayAToB, RelayBToA> HasTwoWayRelay
    for TwoWayRelayContext<Relayer, RelayAToB, RelayBToA>
where
    Relayer: Async,
    Error: Debug + Async,
    RelayAToB: HasRelayTypes<Error = Error>,
    RelayBToA: HasRelayTypes<
        SrcChain = RelayAToB::DstChain,
        DstChain = RelayAToB::SrcChain,
        Error = Error,
    >,
{
    type RelayAToB = RelayAToB;

    type RelayBToA = RelayBToA;

    fn relay_a_to_b(&self) -> &RelayAToB {
        &self.relay_a_to_b
    }

    fn relay_b_to_a(&self) -> &RelayBToA {
        &self.relay_b_to_a
    }

    fn relay_error(e: Error) -> Error {
        e
    }
}

#[async_trait]
impl<Relayer, RelayAToB, RelayBToA> CanAutoRelay
    for TwoWayRelayContext<Relayer, RelayAToB, RelayBToA>
where
    Relayer: AutoRelayer<Self>,
    RelayAToB: Async,
    RelayBToA: Async,
{
    async fn auto_relay(&self) {
        Relayer::auto_relay(self).await;
    }
}
