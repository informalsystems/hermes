use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::ChainConfig;
use ibc_relayer::foreign_client::ForeignClient;

use super::running_node::RunningNode;
use super::wallets::ChainWallets;
use crate::chain::driver::ChainDriver;
use crate::ibc::denom::Denom;
use crate::tagged::*;

pub struct ChainDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub config: ChainConfig,

    pub handle: ChainA,

    pub foreign_client: ForeignClient<ChainB, ChainA>,

    pub running_node: MonoTagged<ChainA, RunningNode>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ChainDeployment<ChainA, ChainB> {
    pub fn chain_id<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainId> {
        self.running_node.chain_id()
    }

    pub fn chain_driver<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainDriver> {
        self.running_node.chain_driver()
    }

    pub fn wallets<'a>(&'a self) -> MonoTagged<ChainA, &'a ChainWallets> {
        self.running_node.wallets()
    }

    pub fn denom<'a>(&'a self) -> MonoTagged<ChainA, &'a Denom> {
        self.running_node.denom()
    }
}
