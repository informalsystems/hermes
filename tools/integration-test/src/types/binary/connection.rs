use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::connection::Connection;

use super::client::ConnectedClients;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::id::ConnectionId;

#[derive(Debug, Clone)]
pub struct ConnectedConnection<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub client: ConnectedClients<ChainA, ChainB>,

    pub connection: Connection<ChainA, ChainB>,

    pub connection_id_a: ConnectionId<ChainA, ChainB>,

    pub connection_id_b: ConnectionId<ChainB, ChainA>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedConnection<ChainA, ChainB> {
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
