use serde::{Deserialize, Serialize};

// use crate::clients::ics07_tendermint::client_state::ClientState; // REVIEW THE NEED TO INCLUDE THE CLIENT STATE IN CONNECTIONHOP
use crate::core::ics03_connection::connection::IdentifiedConnectionEnd;
use crate::core::ics24_host::identifier::ChainId;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionHop {
    pub connection: IdentifiedConnectionEnd,
    // pub client_state: ClientState, // REVIEW THE NEED TO INCLUDE THE CLIENT STATE IN CONNECTIONHOP
    pub reference_chain_id: ChainId,
}

impl ConnectionHop {
    pub fn new(connection: IdentifiedConnectionEnd, reference_chain_id: ChainId) -> Self {
        Self {
            connection,
            reference_chain_id,
        }
    }

    pub fn reference_chain_id(&self) -> ChainId {
        self.reference_chain_id.clone()
    }

    pub fn connection(&self) -> IdentifiedConnectionEnd {
        self.connection.clone()
    }
}

// impl Display for ConnectionHop {
//     todo!();
// }
// impl FromStr for ConnectionHop {
//     todo!();
// }

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionHops {
    pub hops: Vec<ConnectionHop>,
}

impl ConnectionHops {
    pub fn new(hops: Vec<ConnectionHop>) -> Self {
        ConnectionHops { hops }
    }
}
