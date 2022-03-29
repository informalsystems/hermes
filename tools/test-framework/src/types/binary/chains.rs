/*!
   Type definition for two connected chains.
*/

use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use super::foreign_client::ForeignClientPair;
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

    pub foreign_clients: ForeignClientPair<ChainA, ChainB>,
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
        foreign_clients: ForeignClientPair<ChainA, ChainB>,
    ) -> Self {
        Self {
            handle_a,
            handle_b,
            node_a,
            node_b,
            foreign_clients,
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
        self.foreign_clients.client_id_a()
    }

    pub fn client_id_b(&self) -> TaggedClientIdRef<ChainB, ChainA> {
        self.foreign_clients.client_id_b()
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
            foreign_clients: self.foreign_clients.flip(),
        }
    }

    pub fn map_chain<ChainC: ChainHandle, ChainD: ChainHandle>(
        self,
        map_a: &impl Fn(ChainA) -> ChainC,
        map_b: &impl Fn(ChainB) -> ChainD,
    ) -> ConnectedChains<ChainC, ChainD> {
        ConnectedChains {
            handle_a: map_a(self.handle_a),
            handle_b: map_b(self.handle_b),
            node_a: self.node_a.retag(),
            node_b: self.node_b.retag(),
            foreign_clients: self.foreign_clients.map_chain(map_a, map_b),
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
   [`CountingAndCachingChainHandle`](ibc_relayer::chain::handle::CountingAndCachingChainHandle)
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
