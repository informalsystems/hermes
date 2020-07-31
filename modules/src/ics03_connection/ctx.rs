use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics24_host::identifier::ConnectionId;

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
}
