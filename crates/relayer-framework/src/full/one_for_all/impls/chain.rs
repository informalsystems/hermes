use crate::base::one_for_all::traits::chain::OfaChainWrapper;
use crate::base::traits::contexts::telemetry::HasTelemetry;
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;

impl<Chain: OfaFullChain> HasTelemetry for OfaChainWrapper<Chain> {
    type Telemetry = OfaTelemetryWrapper<Chain::Telemetry>;

    fn telemetry(&self) -> &Self::Telemetry {
        self.chain.telemetry()
    }
}
