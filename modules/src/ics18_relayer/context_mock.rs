use crate::context::ChainReader;
use crate::handler::HandlerOutput;
use crate::ics02_client::client_def::{AnyClientState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context_mock::MockClientContext;
use crate::ics02_client::height::{chain_version, Height};
use crate::ics03_connection::context::ConnectionReader;
use crate::ics18_relayer::context::ICS18Context;
use crate::ics18_relayer::error::{Error, Kind};
use crate::ics24_host::identifier::ClientId;
use crate::ics26_routing::context_mock::MockICS26Context;
use crate::ics26_routing::handler::dispatch;
use crate::ics26_routing::msgs::ICS26Envelope;

#[derive(Clone, Debug, Default)]
pub struct MockICS18Context {
    /// Comprises an ICS26 context. Needed to be able to mock the routing of datagrams to a chain.
    pub chain_routing_context: MockICS26Context,
}

impl MockICS18Context {
    /// Create a new ICS18 mock context. This function initializes the context to comprise a chain
    /// with current height corresponding to `chain_height`,  contain
    pub fn new(
        chain_id: String,
        chain_height: u64,
        max_hist_size: usize,
        client_id: &ClientId,
        client_height: u64,
    ) -> MockICS18Context {
        // Create the mock client context.
        let mut client_ctx = MockClientContext::new(
            chain_id.clone(),
            Height {
                version_number: chain_version(chain_id.clone()),
                version_height: chain_height,
            },
            max_hist_size,
        );
        client_ctx.with_client(
            client_id,
            ClientType::Mock,
            Height {
                version_number: chain_version(chain_id),
                version_height: client_height,
            },
        );

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

    /// Internal interface of the context, for consuming (on the modules side) a datagram.
    fn recv(&mut self, msg: ICS26Envelope) -> Result<HandlerOutput<()>, Error> {
        let mut rctx = self.routing_context().clone();
        let res = dispatch(&mut rctx, msg).map_err(|e| Kind::TransactionFailed.context(e))?;
        self.set_routing_context(rctx);
        // Create new block
        self.advance_chain_height();
        Ok(res)
    }
}

impl ICS18Context for MockICS18Context {
    fn query_latest_height(&self) -> Height {
        self.chain_routing_context.host_current_height()
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.chain_routing_context.client_state(client_id)
    }

    fn query_latest_header(&self) -> Option<AnyHeader> {
        let latest_height = self.chain_routing_context.host_current_height();
        self.chain_routing_context
            .chain_context()
            .header(latest_height)
    }

    fn send(&mut self, msg: ICS26Envelope) -> Result<HandlerOutput<()>, Error> {
        self.recv(msg)
    }
}
