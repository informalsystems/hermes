use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::SharedConfig;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::path::PathBuf;

use crate::types::single::client_server::ChainClientServer;

pub struct ConnectedChains<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub config: SharedConfig,

    pub config_path: PathBuf,

    pub registry: SharedRegistry<ProdChainHandle>,

    pub side_a: ChainClientServer<ChainA>,

    pub side_b: ChainClientServer<ChainB>,

    pub client_a_to_b: ForeignClient<ChainB, ChainA>,

    pub client_b_to_a: ForeignClient<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedChains<ChainA, ChainB> {
    pub fn flip(self) -> ConnectedChains<ChainB, ChainA> {
        ConnectedChains {
            config: self.config,
            config_path: self.config_path,
            registry: self.registry,
            client_a_to_b: self.client_b_to_a,
            client_b_to_a: self.client_a_to_b,
            side_a: self.side_b,
            side_b: self.side_a,
        }
    }
}
