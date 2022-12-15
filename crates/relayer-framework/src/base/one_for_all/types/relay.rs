#[derive(Clone)]
pub struct OfaRelayWrapper<Relay> {
    pub relay: Relay,
}

impl<Relay> OfaRelayWrapper<Relay> {
    pub fn new(relay: Relay) -> Self {
        Self { relay }
    }
}
