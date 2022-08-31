use async_trait::async_trait;

use crate::core::traits::queries::status::*;
use crate::core::traits::contexts::telemetry::HasTelemetry;
use crate::core::traits::runtime::telemetry::TelemetryContext;

use crate::std_prelude::*;

pub struct ChainStatusTelemetryQuerier<InQuerier>{
    pub querier: InQuerier,
}

#[async_trait]
impl<InQuerier, Chain, Telemetry> ChainStatusQuerier<Chain> for ChainStatusTelemetryQuerier<InQuerier> 
where 
    InQuerier : ChainStatusQuerier<Chain>,
    Chain: HasTelemetry<Telemetry = Telemetry> + HasChainStatus,
    Telemetry: TelemetryContext
{
    
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error> {
        let telemetry = context.telemetry();
        let label = Telemetry::new_label("key", "value");
        let _ = telemetry.add_counter("query", 1, &[label]); // TODO: Error handling
        let status = InQuerier::query_chain_status(context).await?;
        Ok(status)
    }
}

