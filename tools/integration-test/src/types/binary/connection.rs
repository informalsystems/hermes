/*!
   Type definitions for connection that is connected between two chains.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::connection::Connection;

use super::client::ConnectedClients;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::id::TaggedConnectionId;

/**
   A connection that is connected between two chains with the full
   handshake completed.

   This is a wrapper around [`Connection`] with infallible retrieval
   of the connection IDs, as the connection handshake has been completed.
*/
#[derive(Debug, Clone)]
pub struct ConnectedConnection<ChainA: ChainHandle, ChainB: ChainHandle> {
    /**
       The underlying connected clients
    */
    pub client: ConnectedClients<ChainA, ChainB>,

    /**
       The underlying [`Connection`] data
    */
    pub connection: Connection<ChainA, ChainB>,

    /**
       The connection ID on chain A.
    */
    pub connection_id_a: TaggedConnectionId<ChainA, ChainB>,

    /**
       The connection ID on chain B.
    */
    pub connection_id_b: TaggedConnectionId<ChainB, ChainA>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedConnection<ChainA, ChainB> {
    /**
       Flip the position of chain A and B of the connection.
    */
    pub fn flip(self) -> ConnectedConnection<ChainB, ChainA> {
        ConnectedConnection {
            client: self.client.flip(),

            connection: self.connection.flipped(),

            connection_id_a: self.connection_id_b,

            connection_id_b: self.connection_id_a,
        }
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ExportEnv for ConnectedConnection<ChainA, ChainB> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.client.export_env(writer);
        writer.write_env("CONNECTION_ID_A", &format!("{}", self.connection_id_a));
        writer.write_env("CONNECTION_ID_B", &format!("{}", self.connection_id_b));
    }
}
