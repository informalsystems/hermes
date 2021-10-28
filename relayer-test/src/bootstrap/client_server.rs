use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::chain::handle::ChainHandle;

use super::running_node::RunningNode;
use super::wallets::ChainWallets;
use crate::chain::driver::ChainDriver;
use crate::ibc::denom::Denom;
use crate::tagged::*;

pub struct ChainClientServer<ChainA: ChainHandle> {
    pub handle: ChainA,

    pub node: MonoTagged<ChainA, RunningNode>,
}

impl<ChainA: ChainHandle> ChainClientServer<ChainA> {
    pub fn new(handle: ChainA, node: MonoTagged<ChainA, RunningNode>) -> Self {
        Self { handle, node }
    }

    pub fn chain_id<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainId> {
        self.node.chain_id()
    }

    pub fn chain_driver<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainDriver> {
        self.node.chain_driver()
    }

    pub fn wallets<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainWallets> {
        self.node.wallets()
    }

    pub fn denom<'a>(&'a self) -> MonoTagged<ChainA, &'a Denom> {
        self.node.denom()
    }
}
