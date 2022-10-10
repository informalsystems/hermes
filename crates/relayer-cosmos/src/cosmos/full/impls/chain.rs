use ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::cosmos::base::types::chain::CosmosChainWrapper;
use crate::cosmos::base::types::runtime::CosmosRuntimeContext;
use crate::cosmos::full::traits::chain::CosmosFullChain;
use crate::cosmos::full::types::batch::CosmosBatchChannel;
use crate::cosmos::full::types::telemetry::CosmosTelemetry;

impl<Chain> OfaFullChain for CosmosChainWrapper<Chain>
where
    Chain: CosmosFullChain,
{
    type BatchContext = CosmosRuntimeContext;

    type Telemetry = CosmosTelemetry;

    fn batch_channel(&self) -> &CosmosBatchChannel {
        self.chain.batch_channel()
    }

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry> {
        &self.chain.telemetry()
    }
}
