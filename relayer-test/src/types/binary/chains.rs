/*!
   Type definition for two connected chains.
*/

use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::SharedConfig;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::path::PathBuf;

use crate::types::id::ChainIdRef;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;

/**
   Two connected chains including the [`ChainHandle`], [`ForeignClient`],
   and [`ChainClientServer`].
*/
pub struct ConnectedChains<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub config: SharedConfig,

    pub config_path: PathBuf,

    pub registry: SharedRegistry<ProdChainHandle>,

    pub handle_a: ChainA,

    pub handle_b: ChainB,

    pub node_a: MonoTagged<ChainA, FullNode>,

    pub node_b: MonoTagged<ChainB, FullNode>,

    pub client_a_to_b: ForeignClient<ChainB, ChainA>,

    pub client_b_to_a: ForeignClient<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedChains<ChainA, ChainB> {
    pub fn chain_id_a(&self) -> ChainIdRef<ChainA> {
        self.node_a.chain_id()
    }

    pub fn chain_id_b(&self) -> ChainIdRef<ChainB> {
        self.node_b.chain_id()
    }

    pub fn flip(self) -> ConnectedChains<ChainB, ChainA> {
        ConnectedChains {
            config: self.config,
            config_path: self.config_path,
            registry: self.registry,
            handle_a: self.handle_b,
            handle_b: self.handle_a,
            node_a: self.node_b,
            node_b: self.node_a,
            client_a_to_b: self.client_b_to_a,
            client_b_to_a: self.client_a_to_b,
        }
    }
}
