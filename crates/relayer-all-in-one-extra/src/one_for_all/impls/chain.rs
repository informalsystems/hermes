use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_components_extra::telemetry::traits::telemetry::HasTelemetry;

use crate::one_for_all::traits::chain::OfaFullChain;
use crate::one_for_all::types::telemetry::OfaTelemetryWrapper;

impl<Chain: OfaFullChain> HasTelemetry for OfaChainWrapper<Chain> {
    type Telemetry = OfaTelemetryWrapper<Chain::Telemetry>;

    fn telemetry(&self) -> &Self::Telemetry {
        self.chain.telemetry()
    }
}
