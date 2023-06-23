use alloc::sync::Arc;

pub struct OfaBiRelayWrapper<BiRelay> {
    pub birelay: Arc<BiRelay>,
}

impl<BiRelay> OfaBiRelayWrapper<BiRelay> {
    pub fn new(birelay: BiRelay) -> Self {
        Self {
            birelay: Arc::new(birelay),
        }
    }
}

impl<BiRelay> Clone for OfaBiRelayWrapper<BiRelay> {
    fn clone(&self) -> Self {
        Self {
            birelay: self.birelay.clone(),
        }
    }
}
