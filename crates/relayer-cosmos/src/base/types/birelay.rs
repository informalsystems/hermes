pub struct CosmosBiRelayWrapper<BiRelay> {
    pub birelay: BiRelay,
}

impl<BiRelay> CosmosBiRelayWrapper<BiRelay> {
    pub fn new(birelay: BiRelay) -> Self {
        Self { birelay }
    }
}
