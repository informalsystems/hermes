use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use tokio::task::JoinHandle;

use crate::error::Error;
use crate::prelude::{ConnectedChains, ConnectedChannel, FullNode, TestConfig};
use crate::types::tagged::*;

pub trait HasTwoChains {
    type ChainA: ChainHandle;
    type ChainB: ChainHandle;

    fn chain_a(&self) -> &Self::ChainA;

    fn chain_b(&self) -> &Self::ChainB;

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA>;

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB>;

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB>;
}

pub trait HasTwoNodes: HasTwoChains {
    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode>;

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode>;
}

pub trait HasTestConfig {
    fn config(&self) -> &TestConfig;
}

pub trait HasTwoChannels: HasTwoChains {
    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB>;
}

pub trait CanSpawnRelayer {
    fn spawn_relayer(&self) -> Result<Option<JoinHandle<()>>, Error>;

    fn with_supervisor<R>(&self, cont: impl FnOnce() -> Result<R, Error>) -> Result<R, Error>;
}

pub trait CanWaitForAck: HasTwoChains {
    fn wait_for_src_acks(&self) -> Result<(), Error>;

    fn wait_for_dst_acks(&self) -> Result<(), Error>;
}

pub trait CanShutdown {
    fn shutdown(&self, auto_relay_handle: Option<JoinHandle<()>>);
}

pub trait HasContextId {
    fn context_id(&self) -> String;
}
