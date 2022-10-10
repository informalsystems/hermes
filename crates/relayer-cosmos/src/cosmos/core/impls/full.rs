use ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::cosmos::core::traits::chain::CosmosFullChain;
use crate::cosmos::core::types::batch::CosmosBatchChannel;
use crate::cosmos::core::types::chain::CosmosChainWrapper;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;
use crate::cosmos::core::types::telemetry::CosmosTelemetry;

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
