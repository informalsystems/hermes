use crate::core::ics03_connection::connection::IdentifiedConnectionEnd;
use crate::core::ics24_host::identifier::{ChainId, ConnectionId};

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionHop {
    pub connection: IdentifiedConnectionEnd,
    pub reference_chain_id: ChainId,
}

impl ConnectionHop {
    pub fn new(connection: IdentifiedConnectionEnd, reference_chain_id: ChainId) -> Self {
        Self {
            connection,
            reference_chain_id,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionHops {
    pub hops: Vec<ConnectionHop>,
}

impl ConnectionHops {
    pub fn new(hops: Vec<ConnectionHop>) -> Self {
        ConnectionHops { hops }
    }

    pub fn connection_ids(&self) -> Vec<ConnectionId> {
        self.hops
            .iter()
            .map(|hop| hop.connection.id().clone())
            .collect()
    }
}
