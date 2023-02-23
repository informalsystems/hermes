use ibc_relayer_all_in_one::extra::one_for_all::types::telemetry::OfaTelemetryWrapper;

use crate::base::traits::chain::CosmosChain;
use crate::full::types::telemetry::CosmosTelemetry;

pub trait CosmosFullChain: CosmosChain {
    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry>;
}
