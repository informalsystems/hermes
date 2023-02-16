use async_trait::async_trait;

use crate::base::chain::traits::queries::consensus_state::ConsensusStateQuerier;
use crate::base::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::full::telemetry::traits::metrics::{HasMetric, TelemetryCounter};
use crate::full::telemetry::traits::telemetry::HasTelemetry;

use crate::std_prelude::*;

pub struct ConsensusStateTelemetryQuerier<InQuerier> {
    pub querier: InQuerier,
}

#[async_trait]
impl<InQuerier, Chain, Counterparty, Telemetry> ConsensusStateQuerier<Chain, Counterparty>
    for ConsensusStateTelemetryQuerier<InQuerier>
where
    Chain: HasIbcChainTypes<Counterparty> + HasTelemetry<Telemetry = Telemetry>,
    Counterparty: HasConsensusStateType<Chain>,
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
