use crate::base::core::traits::sync::Async;
use crate::full::batch::types::config::BatchConfig;

pub trait HasBatchConfig: Async {
    fn batch_config(&self) -> &BatchConfig;
}
