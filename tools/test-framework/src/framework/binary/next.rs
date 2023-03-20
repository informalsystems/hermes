use std::thread;

use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_cosmos::base::types::birelay::CosmosBiRelayWrapper;
use ibc_relayer_cosmos::contexts::full::birelay::FullCosmosBiRelay;

use crate::error::Error;
use crate::framework::next::chain::{
    CanSpawnRelayer, HasContextId, HasTestConfig, HasTwoChains, HasTwoChannels, HasTwoNodes,
};
use crate::prelude::{ConnectedChains, ConnectedChannel, FullNode, RelayerDriver, TestConfig};
use crate::types::tagged::*;
use crate::util::suspend::hang_on_error;

/// Test context for the current relayer.
/// Uses a RelayerDriver.
pub struct TestContextV1<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub context_id: String,
    pub config: TestConfig,
    pub relayer: RelayerDriver,
    pub chains: ConnectedChains<ChainA, ChainB>,
    pub channel: ConnectedChannel<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChains for TestContextV1<ChainA, ChainB> {
    type ChainA = ChainA;

    type ChainB = ChainB;

    fn chain_a(&self) -> &Self::ChainA {
        self.chains.handle_a()
    }

    fn chain_b(&self) -> &Self::ChainB {
        self.chains.handle_b()
    }

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA> {
        &self.chains.foreign_clients.client_a_to_b
    }

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB> {
        &self.chains.foreign_clients.client_b_to_a
    }

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB> {
        &self.chains
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoNodes for TestContextV1<ChainA, ChainB> {
    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode> {
        &self.chains.node_a
    }

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode> {
        &self.chains.node_b
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTestConfig for TestContextV1<ChainA, ChainB> {
    fn config(&self) -> &TestConfig {
        &self.config
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChannels for TestContextV1<ChainA, ChainB> {
    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
        &self.channel
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanSpawnRelayer for TestContextV1<ChainA, ChainB> {
    fn spawn_relayer(&self) -> Result<(), Error> {
        let relayer = self.relayer.clone();
        thread::spawn(move || {
            if let Ok(handler) = relayer.spawn_supervisor() {
                handler.wait();
            }
        });

        Ok(())
    }

    fn with_supervisor<R>(&self, cont: impl FnOnce() -> Result<R, Error>) -> Result<R, Error> {
        self.relayer.with_supervisor(cont)
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasContextId for TestContextV1<ChainA, ChainB> {
    fn context_id(&self) -> String {
        self.context_id.clone()
    }
}

/// Test context for the relayer-next.
/// Uses a OfaBiRelayWrapper.
pub struct TestContextV2<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub context_id: String,
    pub config: TestConfig,
    pub relayer: OfaBiRelayWrapper<
        CosmosBiRelayWrapper<FullCosmosBiRelay<BaseChainHandle, BaseChainHandle>>,
    >,
    pub chains: ConnectedChains<ChainA, ChainB>,
    pub channel: ConnectedChannel<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChains for TestContextV2<ChainA, ChainB> {
    type ChainA = ChainA;

    type ChainB = ChainB;

    fn chain_a(&self) -> &Self::ChainA {
        self.chains.handle_a()
    }

    fn chain_b(&self) -> &Self::ChainB {
        self.chains.handle_b()
    }

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA> {
        &self.chains.foreign_clients.client_a_to_b
    }

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB> {
        &self.chains.foreign_clients.client_b_to_a
    }

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB> {
        &self.chains
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoNodes for TestContextV2<ChainA, ChainB> {
    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode> {
        &self.chains.node_a
    }

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode> {
        &self.chains.node_b
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTestConfig for TestContextV2<ChainA, ChainB> {
    fn config(&self) -> &TestConfig {
        &self.config
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChannels for TestContextV2<ChainA, ChainB> {
    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
        &self.channel
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanSpawnRelayer for TestContextV2<ChainA, ChainB> {
    fn spawn_relayer(&self) -> Result<(), Error> {
        let runtime = &self.relayer.birelay.birelay.runtime;
        let relay_contex = self.relayer.clone();

        runtime.runtime.runtime.spawn(async move {
            let _ = relay_contex.auto_relay().await;
        });

        Ok(())
    }

    fn with_supervisor<R>(&self, cont: impl FnOnce() -> Result<R, Error>) -> Result<R, Error> {
        self.spawn_relayer()?;

        hang_on_error(false, cont)
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasContextId for TestContextV2<ChainA, ChainB> {
    fn context_id(&self) -> String {
        self.context_id.clone()
    }
}
