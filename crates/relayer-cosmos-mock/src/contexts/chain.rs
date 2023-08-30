use basecoin_app::modules::ibc::IbcContext;
use basecoin_store::impls::RevertibleStore;
use ibc::core::events::IbcEvent;
use ibc::core::ValidationContext;
use ibc::Any;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;

use std::sync::Arc;

use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;

/// Holds the necessary fields for querying a mock Cosmos
/// chain endpoint.
#[derive(Clone)]
pub struct MockCosmosContext<Endpoint: BasecoinEndpoint> {
    /// Chain runtime
    pub runtime: TokioRuntimeContext,
    /// Chain handle
    pub querier: Arc<Endpoint>,
}

impl<Endpoint: BasecoinEndpoint> MockCosmosContext<Endpoint> {
    /// Constructs a new mock cosmos chain instance.
    pub fn new(runtime: TokioRuntimeContext, querier: Arc<Endpoint>) -> Self {
        Self { runtime, querier }
    }

    pub fn runtime(&self) -> &TokioRuntimeContext {
        &self.runtime
    }

    pub fn ibc_context(
        &self,
    ) -> IbcContext<RevertibleStore<<Endpoint as BasecoinEndpoint>::Store>> {
        self.ibc().ctx()
    }

    pub fn submit_messages(&self, msgs: Vec<Any>) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let mut events = Vec::new();

        self.ibc_context().host_height()?;

        for msg in msgs {
            let ibc_events = self.ibc().process_message(msg)?;

            events.push(ibc_events);
        }

        Ok(events)
    }
}
