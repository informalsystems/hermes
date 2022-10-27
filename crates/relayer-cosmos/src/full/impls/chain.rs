use ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::runtime::CosmosRuntimeContext;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::batch::CosmosBatchChannel;
use crate::full::types::telemetry::CosmosTelemetry;

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
        self.chain.telemetry()
    }
}
