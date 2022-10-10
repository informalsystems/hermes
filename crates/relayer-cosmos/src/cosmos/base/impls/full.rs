use ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::cosmos::base::traits::chain::CosmosFullChain;
use crate::cosmos::base::types::batch::CosmosBatchChannel;
use crate::cosmos::base::types::chain::CosmosChainWrapper;
use crate::cosmos::base::types::runtime::CosmosRuntimeContext;
use crate::cosmos::base::types::telemetry::CosmosTelemetry;

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
