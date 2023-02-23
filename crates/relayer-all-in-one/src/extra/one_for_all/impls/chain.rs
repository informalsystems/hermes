use ibc_relayer_components_extra::telemetry::traits::telemetry::HasTelemetry;

use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::extra::one_for_all::traits::chain::OfaFullChain;
use crate::extra::one_for_all::types::telemetry::OfaTelemetryWrapper;

impl<Chain: OfaFullChain> HasTelemetry for OfaChainWrapper<Chain> {
    type Telemetry = OfaTelemetryWrapper<Chain::Telemetry>;

    fn telemetry(&self) -> &Self::Telemetry {
        self.chain.telemetry()
    }
}
