pub struct CosmosRelayWrapper<Relay> {
    pub relay: Relay,
}

impl<Relay> CosmosRelayWrapper<Relay> {
    pub fn new(relay: Relay) -> Self {
        Self { relay }
    }
}
