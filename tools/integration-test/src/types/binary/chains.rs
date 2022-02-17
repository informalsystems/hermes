/*!
   Type definition for two connected chains.
*/

use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::SharedConfig;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::path::PathBuf;
use tracing::info;

use crate::relayer::foreign_client::TaggedForeignClientExt;
use crate::types::env::{prefix_writer, EnvWriter, ExportEnv};
use crate::types::id::{TaggedChainIdRef, TaggedClientIdRef};
use crate::types::single::node::{FullNode, TaggedFullNodeExt};
use crate::types::tagged::*;

/**
   Two connected chains including the full node, chain handles, and
   the corresponding foreign clients.
*/
#[derive(Clone)]
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
       [`spawn_supervisor`](ibc_relayer::supervisor::spawn_supervisor).
    */
    pub config: SharedConfig,

    /**
       The relayer chain [`Registry`](ibc_relayer::registry::Registry)
       that is shared with any running
       [supervisor](ibc_relayer::supervisor::SupervisorHandle).

       Use this shared registry when spawning new supervisor using
       [`spawn_supervisor`](ibc_relayer::supervisor::spawn_supervisor).
    */
    pub registry: SharedRegistry<ProdChainHandle>,

    /**
        The [`ChainHandle`] for chain A.

        The handle is wrapped in [`DropChainHandle`] to stop the chain
        handle when this is dropped.
    */
    pub handle_a: ChainA,

    /**
        The [`ChainHandle`] for chain B.

        The handle is wrapped in [`DropChainHandle`] to stop the chain
        handle when this is dropped.
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
       Create a new [`ConnectedChains`]
    */
    pub fn new(
        config_path: PathBuf,
        config: SharedConfig,
        registry: SharedRegistry<ProdChainHandle>,
        handle_a: ChainA,
        handle_b: ChainB,
        node_a: MonoTagged<ChainA, FullNode>,
        node_b: MonoTagged<ChainB, FullNode>,
        client_a_to_b: ForeignClient<ChainB, ChainA>,
        client_b_to_a: ForeignClient<ChainA, ChainB>,
    ) -> Self {
        Self {
            config_path,
            config,
            registry,
            handle_a,
            handle_b,
            node_a,
            node_b,
            client_a_to_b,
            client_b_to_a,
        }
    }

    /**
      Get a reference to the chain handle for chain A.
    */
    pub fn handle_a(&self) -> &ChainA {
        &self.handle_a
    }

    /**
      Get a reference to the chain handle for chain B.
    */
    pub fn handle_b(&self) -> &ChainB {
        &self.handle_b
    }

    /**
       The chain ID of chain A.
    */
    pub fn chain_id_a(&self) -> TaggedChainIdRef<ChainA> {
        self.node_a.chain_id()
    }

    pub fn client_id_a(&self) -> TaggedClientIdRef<ChainA, ChainB> {
        self.client_b_to_a.tagged_client_id()
    }

    pub fn client_id_b(&self) -> TaggedClientIdRef<ChainB, ChainA> {
        self.client_a_to_b.tagged_client_id()
    }

    /**
       The chain ID of chain B.
    */
    pub fn chain_id_b(&self) -> TaggedChainIdRef<ChainB> {
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

impl<ChainA: ChainHandle, ChainB: ChainHandle> ExportEnv for ConnectedChains<ChainA, ChainB> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("RELAYER_CONFIG", &format!("{}", self.config_path.display()));

        writer.write_env("CHAIN_ID_A", &format!("{}", self.node_a.chain_id()));
        writer.write_env("CHAIN_ID_B", &format!("{}", self.node_b.chain_id()));

        self.node_a.export_env(&mut prefix_writer("NODE_A", writer));
        self.node_b.export_env(&mut prefix_writer("NODE_B", writer));
    }
}

/**
   Newtype wrapper for [`ChainHandle`] to stop the chain handle when
   this value is dropped.

   Note that we cannot stop the chain on drop for
   [`ProdChainHandle`](ibc_relayer::chain::handle::ProdChainHandle)
   itself, as the chain handles can be cloned. But for testing purposes,
   we alway stop the chain handle when this "canonical" chain handle
   is dropped.

   This is necessary as otherwise the chain handle will display error
   logs when the full node is terminated at the end of tests.
*/
pub struct DropChainHandle<Chain: ChainHandle>(pub Chain);

impl<Chain: ChainHandle> Drop for DropChainHandle<Chain> {
    fn drop(&mut self) {
        info!("stopping chain handle {}", self.0.id());
        let _ = self.0.shutdown();
    }
}
