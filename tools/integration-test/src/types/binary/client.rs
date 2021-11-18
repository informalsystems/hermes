/*!
   Type definitions for IBC clients connected between two chains.
*/

use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::id::TaggedClientId;

/**
   Data type to store the client IDs of two chains that are connected.
*/
#[derive(Debug, Clone)]
pub struct ConnectedClients<ChainA, ChainB> {
    /**
       The client ID on chain A.
    */
    pub client_id_a: TaggedClientId<ChainA, ChainB>,

    /**
       The client ID on chain B.
    */
    pub client_id_b: TaggedClientId<ChainB, ChainA>,
}

impl<ChainA, ChainB> ConnectedClients<ChainA, ChainB> {
    /**
       Flip the position of chain A and B of the client.
    */
    pub fn flip(self) -> ConnectedClients<ChainB, ChainA> {
        ConnectedClients {
            client_id_a: self.client_id_b,
            client_id_b: self.client_id_a,
        }
    }
}

impl<ChainA, ChainB> ExportEnv for ConnectedClients<ChainA, ChainB> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("CLIENT_ID_A", &format!("{}", self.client_id_a));
        writer.write_env("CLIENT_ID_B", &format!("{}", self.client_id_b));
    }
}
