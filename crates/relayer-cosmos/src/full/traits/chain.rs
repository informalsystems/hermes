use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::base::traits::chain::CosmosChain;
use crate::full::types::batch::CosmosBatchChannel;
use crate::full::types::telemetry::CosmosTelemetry;

pub trait CosmosFullChain: CosmosChain {
    fn batch_channel(&self) -> &CosmosBatchChannel;

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry>;
}
