use ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;

use crate::base::types::chain::CosmosChainWrapper;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::telemetry::CosmosTelemetry;

impl<Chain> OfaFullChain for CosmosChainWrapper<Chain>
where
    Chain: CosmosFullChain,
{
    type Telemetry = CosmosTelemetry;

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry> {
        self.chain.telemetry()
    }
}
