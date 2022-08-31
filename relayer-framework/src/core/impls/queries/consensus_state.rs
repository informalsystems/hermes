use async_trait::async_trait;

use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::telemetry::HasTelemetry;
use crate::core::traits::queries::consensus_state::*;
use crate::core::traits::runtime::telemetry::TelemetryContext;

use crate::std_prelude::*;

pub struct ConsensusStateTelemetryQuerier<InQuerier> {
    pub querier: InQuerier,
}

#[async_trait]
impl<InQuerier, Chain, Counterparty, Telemetry> ConsensusStateQuerier<Chain, Counterparty>
    for ConsensusStateTelemetryQuerier<InQuerier>
where
    Chain: IbcChainContext<Counterparty> + HasTelemetry<Telemetry = Telemetry>,
    Counterparty: HasConsensusState<Chain>,
    InQuerier: ConsensusStateQuerier<Chain, Counterparty>,
    Telemetry: TelemetryContext,
{
    async fn query_consensus_state(
        chain: &Chain,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error> {
        let telemetry = chain.telemetry();
        let label = Telemetry::new_label("consensus_state_query", "value");
        let _ = telemetry.add_counter("query", 1, &[label]); // TODO: Error handling
        let status = InQuerier::query_consensus_state(chain, client_id, height).await?;
        Ok(status)
    }
}
