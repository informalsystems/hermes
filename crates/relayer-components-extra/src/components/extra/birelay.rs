use core::marker::PhantomData;

use crate::relay::components::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;
use ibc_relayer_components::relay::traits::auto_relayer::{AutoRelayerComponent, BiRelayMode};
pub struct ExtraBiRelayComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_component!(
    AutoRelayerComponent<BiRelayMode>,
    ExtraBiRelayComponents<BaseComponents>,
    ParallelTwoWayAutoRelay,
);
