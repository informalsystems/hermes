pub struct CosmosFullBuilderWrapper<Builder> {
    pub builder: Builder,
}

impl<Builder> CosmosFullBuilderWrapper<Builder> {
    pub fn new(builder: Builder) -> Self {
        Self { builder }
    }
}
