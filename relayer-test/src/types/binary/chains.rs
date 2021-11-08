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
   Two connected chains including the full node, chain handles, and
   the corresponding foreign clients.
*/
pub struct ConnectedChains<ChainA: ChainHandle, ChainB: ChainHandle> {
    /**
       The path to the relayer config saved on the filesystem.

       This allows users to test the relayer manually with the config file
       while the test is suspended.
    */
    pub config_path: PathBuf,

    /**
       The relayer [`Config`](ibc_relayer::config::Config) that is shared
       with the [`Registry`](ibc_relayer::registry::Registry).

       Use this shared config when spawning new supervisor using
       [`spawn_supervisor`](crate::relayer::supervisor::spawn_supervisor).
    */
    pub config: SharedConfig,

    /**
       The relayer chain [`Registry`](ibc_relayer::registry::Registry)
       that is shared with any running
       [`Supervisor`](ibc_relayer::supervisor::Supervisor).

       Use this shared registry when spawning new supervisor using
       [`spawn_supervisor`](crate::relayer::supervisor::spawn_supervisor).
    */
    pub registry: SharedRegistry<ProdChainHandle>,

    /**
        The [`ChainHandle`] for chain A.
    */
    pub handle_a: ChainA,

    /**
        The [`ChainHandle`] for chain B.
    */
    pub handle_b: ChainB,

    /**
       The tagged [`FullNode`] for chain A.
    */
    pub node_a: MonoTagged<ChainA, FullNode>,

    /**
       The tagged [`FullNode`] for chain B.
    */
    pub node_b: MonoTagged<ChainB, FullNode>,

    /**
       The [`ForeignClient`] from chain A to chain B.

       Note that the type parameter for [`ForeignClient`]
       have the destination chain placed at first position.
    */
    pub client_a_to_b: ForeignClient<ChainB, ChainA>,

    /**
       The [`ForeignClient`] from chain B to chain A.

       Note that the type parameter for [`ForeignClient`]
       have the destination chain placed at first position.
    */
    pub client_b_to_a: ForeignClient<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedChains<ChainA, ChainB> {
    /**
       The chain ID of chain A.
    */
    pub fn chain_id_a(&self) -> ChainIdRef<ChainA> {
        self.node_a.chain_id()
    }

    /**
       The chain ID of chain B.
    */
    pub fn chain_id_b(&self) -> ChainIdRef<ChainB> {
        self.node_b.chain_id()
    }

    /**
       Switch the position between chain A and chain B.

       The original chain B become the new chain A, and the original chain A
       become the new chain B.
    */
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
