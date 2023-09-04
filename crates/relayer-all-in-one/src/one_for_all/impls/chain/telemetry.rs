use ibc_relayer_components_extra::telemetry::traits::telemetry::HasTelemetry;

use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;

impl<Chain> HasTelemetry for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    type Telemetry = Chain::Telemetry;

    fn telemetry(&self) -> &Self::Telemetry {
        self.chain.telemetry()
    }
}
