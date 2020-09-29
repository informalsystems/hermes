use crate::ics02_client::client_def::AnyClientState;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context_mock::MockClientContext;
use crate::ics03_connection::context::ConnectionReader;
use crate::ics18_relayer::context::ICS18Context;
use crate::ics24_host::identifier::ClientId;
use crate::ics26_routing::context_mock::MockICS26Context;
use crate::Height;

#[derive(Clone, Debug, Default)]
pub struct MockICS18Context {
    /// Comprises an ICS26 context. Needed to be able to mock the routing of datagrams to a chain.
    pub chain_routing_context: MockICS26Context,
}

impl MockICS18Context {
    /// Create a new ICS18 mock context. This function initializes the context to comprise a chain
    /// with current height corresponding to `chain_height`,  contain
    pub fn new(
        chain_height: Height,
        max_hist_size: usize,
        client_id: &ClientId,
        client_height: Height,
    ) -> MockICS18Context {
        // Create the mock client context.
        let mut client_ctx = MockClientContext::new(u64::from(chain_height), max_hist_size);
        client_ctx.with_client(client_id, ClientType::Mock, client_height);

        Self {
            // Wrap the client context in a ICS26 context, which we wrap in the ICS18 context.
            chain_routing_context: MockICS26Context {
                client_context: client_ctx,
                connection_context: Default::default(), // This parameter is ignored for the purpose of this mock.
            },
        }
    }

    pub fn routing_context(&self) -> &MockICS26Context {
        &self.chain_routing_context
    }

    pub fn set_routing_context(&mut self, new_rc: MockICS26Context) {
        self.chain_routing_context = new_rc
    }

    pub fn advance_chain_height(&mut self) {
        let mut underlying_chain_ctx = self.chain_routing_context.chain_context().clone();
        underlying_chain_ctx.add_header(0);
        // Replace the chain context with the newer one.
        self.chain_routing_context
            .set_chain_context(underlying_chain_ctx)
    }
}

impl ICS18Context for MockICS18Context {
    fn query_latest_height(&self) -> Height {
        self.chain_routing_context.chain_current_height()
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.chain_routing_context.fetch_client_state(client_id)
    }
}
