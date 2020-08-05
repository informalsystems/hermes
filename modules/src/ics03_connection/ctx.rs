use crate::ics02_client::state::ClientState;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::error::Error;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics24_host::introspect::{current_height, get_commitment_prefix, trusting_period};
use crate::Height;

// TODO: Remove this once Romain's code kicks in.
pub struct Chain {}

// TODO: Both ICS3Context & Context should be generic over Chain.
pub struct Context {
    local_chain: Chain,
}

/// A context supplying all the necessary dependencies for processing any `ICS3Msg`.
pub trait ICS3Context {
    /// Returns the ConnectionEnd for the given identifier `conn_id`.
    fn fetch_connection_end_by_id(&self, conn_id: &ConnectionId) -> Option<&ConnectionEnd>;

    /// Returns the ClientState for the given identifier `client_id`.
    fn fetch_client_state_by_id(
        &self,
        client_id: &ClientId,
    ) -> Option<&dyn ClientState<ValidationError = Error>>;

    /// Returns the current height of the local chain.
    /// Satisfies the ICS024 requirement of getCurrentHeight().
    fn chain_current_height(&self) -> Height;

    /// Returns the trusting period (in number of block) for the local chain.
    fn chain_trusting_period(&self) -> Height;

    /// Returns the prefix that the local chain uses in the KV store.
    /// Satisfies the ICS024 requirement of getCommitmentPrefix().
    fn commitment_prefix(&self) -> CommitmentPrefix;
}

impl ICS3Context for Context {
    fn fetch_connection_end_by_id(&self, _cid: &ConnectionId) -> Option<&ConnectionEnd> {
        unimplemented!()
    }

    fn fetch_client_state_by_id(
        &self,
        _client_id: &ClientId,
    ) -> Option<&dyn ClientState<ValidationError = Error>> {
        unimplemented!()
    }

    fn chain_current_height(&self) -> Height {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        current_height()
    }

    fn chain_trusting_period(&self) -> Height {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        trusting_period()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        get_commitment_prefix()
    }
}
