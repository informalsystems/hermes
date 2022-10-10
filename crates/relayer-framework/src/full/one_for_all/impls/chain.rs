use crate::base::one_for_all::traits::chain::OfaChainWrapper;
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;
use crate::full::telemetry::traits::telemetry::HasTelemetry;

impl<Chain: OfaFullChain> HasTelemetry for OfaChainWrapper<Chain> {
    type Telemetry = OfaTelemetryWrapper<Chain::Telemetry>;

    fn telemetry(&self) -> &Self::Telemetry {
        self.chain.telemetry()
    }
}
