use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::ConnectionId;
use crate::ics24_host::introspect::{current_height, get_commitment_prefix, trusting_period};
use crate::Height;

// TODO: Remove this once Romain's code kicks in.
pub struct Chain {}

// TODO: Introduce a Context. Both ICS3Context & Context should be traits generic over Chain.
pub struct ICS3Context {
    local_chain: Chain,
}

/// A context supplying all the necessary dependencies for processing any `ICS3Msg`.
impl ICS3Context {
    /// Returns a ConnectionEnd with connection_id for the `ICS3Msg` being currently processed.
    pub fn current_connection(&self) -> Option<&ConnectionEnd> {
        unimplemented!()
    }

    pub fn current_connection_id(&self) -> &ConnectionId {
        unimplemented!()
    }

    /// Returns the current height of the local chain.
    /// Satisfies the ICS024 requirement of getCurrentHeight().
    pub fn chain_current_height(&self) -> Height {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        current_height()
    }

    /// Returns the trusting period (in number of block) for the local chain.
    pub fn chain_trusting_period(&self) -> Height {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        trusting_period()
    }

    /// Returns the prefix that the local chain uses in the KV store.
    /// Satisfies the ICS024 requirement of getCommitmentPrefix().
    pub fn commitment_prefix(&self) -> CommitmentPrefix {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        get_commitment_prefix()
    }
}
