use async_trait::async_trait;
use ibc_relayer_components::chain::traits::components::chain_status_querier::*;
use ibc_relayer_components::chain::traits::types::status::HasChainStatusType;
use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::std_prelude::*;
use crate::telemetry::traits::metrics::{HasMetric, TelemetryCounter};
use crate::telemetry::traits::telemetry::HasTelemetry;

pub struct ChainStatusTelemetryQuerier<InQuerier> {
    pub querier: InQuerier,
}

#[async_trait]
impl<InQuerier, Chain, Telemetry> ChainStatusQuerier<Chain>
    for ChainStatusTelemetryQuerier<InQuerier>
where
    InQuerier: ChainStatusQuerier<Chain>,
    Chain: HasChainStatusType + HasTelemetry<Telemetry = Telemetry> + HasErrorType,
    Telemetry: HasMetric<TelemetryCounter>,
    Telemetry::Value: From<u64>,
{
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error> {
        let telemetry = context.telemetry();
        let label = Telemetry::new_label("query_type", "status");
        telemetry.update_metric("query", &[label], 1u64.into(), None, None);
        let status = InQuerier::query_chain_status(context).await?;
        Ok(status)
    }
}
