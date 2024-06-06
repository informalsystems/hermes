use crate::core::ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd};
use crate::core::ics24_host::identifier::{ChainId, ConnectionId};

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionHop {
    pub connection: IdentifiedConnectionEnd,
    pub src_chain_id: ChainId,
    pub dst_chain_id: ChainId,
}

impl ConnectionHop {
    pub fn new(
        connection: IdentifiedConnectionEnd,
        src_chain_id: ChainId,
        dst_chain_id: ChainId,
    ) -> Self {
        Self {
            connection,
            src_chain_id,
            dst_chain_id,
        }
    }

    pub fn connection(&self) -> &ConnectionEnd {
        &self.connection.connection_end
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

    pub fn hops_as_slice(&self) -> &[ConnectionHop] {
        &self.hops
    }
}
