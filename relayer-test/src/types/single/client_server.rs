use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::chain::driver::ChainDriver;
use crate::ibc::denom::Denom;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::types::wallet::TestWallets;

pub struct ChainClientServer<ChainA: ChainHandle> {
    pub handle: ChainA,

    pub node: MonoTagged<ChainA, FullNode>,
}

impl<ChainA: ChainHandle> ChainClientServer<ChainA> {
    pub fn new(handle: ChainA, node: FullNode) -> Self {
        Self {
            handle,
            node: MonoTagged::new(node),
        }
    }

    pub fn chain_id<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainId> {
        self.node.chain_id()
    }

    pub fn chain_driver<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainDriver> {
        self.node.chain_driver()
    }

    pub fn wallets<'a>(&'a self) -> MonoTagged<ChainA, &'a TestWallets> {
        self.node.wallets()
    }

    pub fn denom<'a>(&'a self) -> MonoTagged<ChainA, &'a Denom> {
        self.node.denom()
    }
}

impl<Chain: ChainHandle> Drop for ChainClientServer<Chain> {
    fn drop(&mut self) {
        let _ = self.handle.shutdown();
    }
}
