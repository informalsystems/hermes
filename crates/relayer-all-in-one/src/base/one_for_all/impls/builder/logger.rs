use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};

use crate::base::one_for_all::traits::builder::OfaBuilder;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;

impl<Build> HasLoggerType for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type Logger = Build::Logger;
}

impl<Build> HasLogger for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    fn logger(&self) -> &Self::Logger {
        self.builder.logger()
    }
}
