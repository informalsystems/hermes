use crate::full::batch::traits::config::HasBatchConfig;
use crate::full::batch::types::config::BatchConfig;
use crate::full::one_for_all::traits::builder::OfaFullBuilder;
use crate::full::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder> HasBatchConfig for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
{
    fn batch_config(&self) -> &BatchConfig {
        self.builder.batch_config()
    }
}
