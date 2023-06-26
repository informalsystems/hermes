use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> HasLoggerType for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    type Logger = Relay::Logger;
}

impl<Relay> HasLogger for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn logger(&self) -> &Self::Logger {
        self.relay.logger()
    }
}
