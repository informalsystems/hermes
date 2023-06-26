use ibc_relayer_components_extra::batch::traits::config::HasBatchConfig;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;

use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::builder::OfaBuilderWrapper;

impl<Builder> HasBatchConfig for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    fn batch_config(&self) -> &BatchConfig {
        self.builder.batch_config()
    }
}
