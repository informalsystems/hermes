use ibc_relayer_components_extra::batch::traits::config::HasBatchConfig;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;

use crate::one_for_all::traits::builder::OfaFullBuilder;
use crate::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder> HasBatchConfig for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
{
    fn batch_config(&self) -> &BatchConfig {
        self.builder.batch_config()
    }
}
