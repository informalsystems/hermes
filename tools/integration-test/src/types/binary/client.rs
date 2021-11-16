use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::id::ClientId;

#[derive(Debug, Clone)]
pub struct ConnectedClients<ChainA, ChainB> {
    pub client_id_a: ClientId<ChainA, ChainB>,
    pub client_id_b: ClientId<ChainB, ChainA>,
}

impl<ChainA, ChainB> ConnectedClients<ChainA, ChainB> {
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
