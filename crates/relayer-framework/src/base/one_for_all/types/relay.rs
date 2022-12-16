use alloc::sync::Arc;

pub struct OfaRelayWrapper<Relay> {
    pub relay: Arc<Relay>,
}

impl<Relay> OfaRelayWrapper<Relay> {
    pub fn new(relay: Relay) -> Self {
        Self {
            relay: Arc::new(relay),
        }
    }
}

impl<Relay> Clone for OfaRelayWrapper<Relay> {
    fn clone(&self) -> Self {
        Self {
            relay: self.relay.clone(),
        }
    }
}
