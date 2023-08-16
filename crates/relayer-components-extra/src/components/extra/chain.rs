use core::marker::PhantomData;
use ibc_relayer_components::chain::traits::message_sender::MessageSenderComponent;
use ibc_relayer_components::chain::traits::queries::consensus_state::ConsensusStateQuerierComponent;
use ibc_relayer_components::chain::traits::queries::status::ChainStatusQuerierComponent;
use ibc_relayer_components::components::default::chain::DefaultChainComponents;

use crate::telemetry::components::consensus_state::ConsensusStateTelemetryQuerier;
use crate::telemetry::components::status::ChainStatusTelemetryQuerier;

pub struct ExtraChainComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_component!(
    ChainStatusQuerierComponent,
    ExtraChainComponents<BaseComponents>,
    ChainStatusTelemetryQuerier<BaseComponents>,
);

ibc_relayer_components::delegate_component!(
    ConsensusStateQuerierComponent,
    ExtraChainComponents<BaseComponents>,
    ConsensusStateTelemetryQuerier<BaseComponents>,
);

ibc_relayer_components::delegate_components!(
    [MessageSenderComponent,],
    ExtraChainComponents<BaseComponents>,
    DefaultChainComponents<BaseComponents>,
);
