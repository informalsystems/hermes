pub struct CosmosBuilderWrapper<Builder> {
    pub builder: Builder,
}

impl<Builder> CosmosBuilderWrapper<Builder> {
    pub fn new(builder: Builder) -> Self {
        Self { builder }
    }
}
