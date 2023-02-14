use alloc::sync::Arc;

use crate::base::one_for_all::traits::builder::OfaBuilderTypes;

pub struct OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    pub builder: Arc<Builder>,
}

impl<Builder> OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    pub fn new(builder: Builder) -> Self {
        Self {
            builder: Arc::new(builder),
        }
    }
}

impl<Builder> Clone for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    fn clone(&self) -> Self {
        Self {
            builder: self.builder.clone(),
        }
    }
}
