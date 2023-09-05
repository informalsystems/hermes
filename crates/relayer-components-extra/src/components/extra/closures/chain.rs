use ibc_relayer_components::chain::traits::components::chain_status_querier::{
    CanQueryChainStatus, ChainStatusQuerier,
};
use ibc_relayer_components::chain::traits::components::consensus_state_querier::{
    CanQueryConsensusState, ConsensusStateQuerier,
};
use ibc_relayer_components::chain::traits::components::message_sender::{
    CanSendMessages, MessageSender,
};
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::height::HasHeightType;
use ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes;
use ibc_relayer_components::chain::traits::types::status::HasChainStatusType;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::components::extra::chain::ExtraChainComponents;
use crate::telemetry::traits::metrics::HasBasicMetrics;
use crate::telemetry::traits::telemetry::HasTelemetry;

pub trait UseExtraChainComponents<Counterparty>:
    CanQueryChainStatus + CanQueryConsensusState<Counterparty> + CanSendMessages
where
    Counterparty: HasHeightType + HasConsensusStateType<Self>,
{
}

impl<Chain, Counterparty, BaseComponents> UseExtraChainComponents<Counterparty> for Chain
where
    Counterparty: HasHeightType + HasConsensusStateType<Chain>,
    Chain: HasErrorType
        + HasTelemetry
        + HasChainStatusType
        + HasIbcChainTypes<Counterparty>
        + HasComponents<Components = ExtraChainComponents<BaseComponents>>,
    Chain::Telemetry: HasBasicMetrics,
    BaseComponents: MessageSender<Chain>
        + ChainStatusQuerier<Chain>
        + ConsensusStateQuerier<Chain, Counterparty>,
{
}
