use async_trait::async_trait;
use ibc_relayer_components::chain::traits::components::consensus_state_querier::ConsensusStateQuerier;
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::height::HasHeightType;
use ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes;
use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::std_prelude::*;
use crate::telemetry::traits::metrics::{HasMetric, TelemetryCounter};
use crate::telemetry::traits::telemetry::HasTelemetry;

pub struct ConsensusStateTelemetryQuerier<InQuerier> {
    pub querier: InQuerier,
}

#[async_trait]
impl<InQuerier, Chain, Counterparty, Telemetry> ConsensusStateQuerier<Chain, Counterparty>
    for ConsensusStateTelemetryQuerier<InQuerier>
where
    Chain: HasIbcChainTypes<Counterparty> + HasTelemetry<Telemetry = Telemetry> + HasErrorType,
    Counterparty: HasConsensusStateType<Chain> + HasHeightType,
    InQuerier: ConsensusStateQuerier<Chain, Counterparty>,
    Telemetry: HasMetric<TelemetryCounter>,
    Telemetry::Value: From<u64>,
{
    async fn query_consensus_state(
        chain: &Chain,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error> {
        let telemetry = chain.telemetry();
        let label = Telemetry::new_label("query_type", "consensus_state");
        telemetry.update_metric("query", &[label], 1u64.into(), None, None);
        let status = InQuerier::query_consensus_state(chain, client_id, height).await?;
        Ok(status)
    }
}
