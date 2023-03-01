use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};

use crate::base::one_for_all::traits::chain::OfaBaseChain;
use crate::base::one_for_all::types::chain::OfaChainWrapper;

impl<Chain> HasLoggerType for OfaChainWrapper<Chain>
where
    Chain: OfaBaseChain,
{
    type Logger = Chain::Logger;
}

impl<Chain> HasLogger for OfaChainWrapper<Chain>
where
    Chain: OfaBaseChain,
{
    fn logger(&self) -> &Self::Logger {
        self.chain.logger()
    }
}
