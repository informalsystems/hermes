use core::marker::PhantomData;

use crate::relay::components::auto_relayers::concurrent_two_way::ConcurrentTwoWayAutoRelay;
use crate::relay::traits::auto_relayer::{AutoRelayerComponent, BiRelayMode};
pub struct DefaultBiRelayComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    AutoRelayerComponent<BiRelayMode>,
    DefaultBiRelayComponents<BaseComponents>,
    ConcurrentTwoWayAutoRelay,
);
