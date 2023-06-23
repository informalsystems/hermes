use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> HasLoggerType for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
{
    type Logger = Relay::Logger;
}

impl<Relay> HasLogger for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
{
    fn logger(&self) -> &Self::Logger {
        self.relay.logger()
    }
}
