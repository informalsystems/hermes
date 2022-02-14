/*!
   Type definition for two connected chains.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
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
        handle_a: ChainA,
        handle_b: ChainB,
        node_a: MonoTagged<ChainA, FullNode>,
        node_b: MonoTagged<ChainB, FullNode>,
        client_a_to_b: ForeignClient<ChainB, ChainA>,
        client_b_to_a: ForeignClient<ChainA, ChainB>,
    ) -> Self {
        Self {
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
            handle_a: self.handle_b,
            handle_b: self.handle_a,
            node_a: self.node_b,
            node_b: self.node_a,
            client_a_to_b: self.client_b_to_a,
            client_b_to_a: self.client_a_to_b,
        }
    }

    pub fn map_chain<ChainC: ChainHandle, ChainD: ChainHandle>(
        self,
        map_a: impl Fn(ChainA) -> ChainC,
        map_b: impl Fn(ChainB) -> ChainD,
    ) -> ConnectedChains<ChainC, ChainD> {
        ConnectedChains {
            handle_a: map_a(self.handle_a),
            handle_b: map_b(self.handle_b),
            node_a: self.node_a.retag(),
            node_b: self.node_b.retag(),
            client_a_to_b: self.client_a_to_b.map_chain(&map_b, &map_a),
            client_b_to_a: self.client_b_to_a.map_chain(&map_a, &map_b),
        }
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ExportEnv for ConnectedChains<ChainA, ChainB> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
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
