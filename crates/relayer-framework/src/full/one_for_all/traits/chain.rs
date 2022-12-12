use crate::base::one_for_all::traits::chain::OfaBaseChain;
use crate::full::one_for_all::traits::telemetry::{OfaTelemetry, OfaTelemetryWrapper};

pub trait OfaFullChain: OfaBaseChain {
    type Telemetry: OfaTelemetry;

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry>;
}
