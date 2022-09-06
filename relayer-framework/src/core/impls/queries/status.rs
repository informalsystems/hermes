use async_trait::async_trait;

use crate::core::traits::contexts::telemetry::HasTelemetry;
use crate::core::traits::queries::status::*;

use crate::one_for_all::traits::telemetry::OfaTelemetry;
use crate::std_prelude::*;

pub struct ChainStatusTelemetryQuerier<InQuerier> {
    pub querier: InQuerier,
}

#[async_trait]
impl<InQuerier, Chain, Telemetry> ChainStatusQuerier<Chain>
    for ChainStatusTelemetryQuerier<InQuerier>
where
    InQuerier: ChainStatusQuerier<Chain>,
    Chain: HasTelemetry<Telemetry = Telemetry> + HasChainStatus,
    Telemetry: OfaTelemetry,
{
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error> {
        let telemetry = context.telemetry();
        let label = Telemetry::new_label("query_type", "status");
        telemetry.update_counter_metric("query", &[label], 1u64.into(), None, None);
        let status = InQuerier::query_chain_status(context).await?;
        Ok(status)
    }
}
