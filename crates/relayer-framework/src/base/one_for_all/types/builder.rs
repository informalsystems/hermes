use alloc::sync::Arc;

pub struct OfaBuilderWrapper<Builder> {
    pub builder: Arc<Builder>,
}

impl<Builder> OfaBuilderWrapper<Builder> {
    pub fn new(builder: Builder) -> Self {
        Self {
            builder: Arc::new(builder),
        }
    }
}

impl<Builder> Clone for OfaBuilderWrapper<Builder> {
    fn clone(&self) -> Self {
        Self {
            builder: self.builder.clone(),
        }
    }
}
