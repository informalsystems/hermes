use ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::types::chain::CosmosChainWrapper;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::batch::CosmosBatchChannel;
use crate::full::types::telemetry::CosmosTelemetry;

impl<Chain> OfaFullChain for CosmosChainWrapper<Chain>
where
    Chain: CosmosFullChain,
{
    type BatchContext = TokioRuntimeContext;

    type Telemetry = CosmosTelemetry;

    fn batch_channel(&self) -> &CosmosBatchChannel {
        self.chain.batch_channel()
    }

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry> {
        self.chain.telemetry()
    }
}
