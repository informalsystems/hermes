use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};

use crate::base::one_for_all::traits::birelay::OfaBiRelay;
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;

impl<BiRelay> HasLoggerType for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: OfaBiRelay,
{
    type Logger = BiRelay::Logger;
}

impl<BiRelay> HasLogger for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: OfaBiRelay,
{
    fn logger(&self) -> &Self::Logger {
        self.birelay.logger()
    }
}
