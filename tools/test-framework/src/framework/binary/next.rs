use std::thread;

use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_cosmos::base::types::birelay::CosmosBiRelayWrapper;
use ibc_relayer_cosmos::contexts::full::birelay::FullCosmosBiRelay;

use crate::error::Error;
use crate::framework::next::chain::{CanSpawnRelayer, HasContextId, HasTwoChains, HasTwoChannels};
use crate::prelude::{ConnectedChains, ConnectedChannel, FullNode, RelayerDriver, TestConfig};
use crate::types::tagged::*;

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

    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode> {
        &self.chains.node_a
    }

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode> {
        &self.chains.node_b
    }

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA> {
        &self.chains.foreign_clients.client_a_to_b
    }

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB> {
        &self.chains.foreign_clients.client_b_to_a
    }

    fn config(&self) -> &TestConfig {
        &self.config
    }

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB> {
        &self.chains
    }

    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
        &self.channel
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChannels for TestContextV1<ChainA, ChainB> {
    fn channel_a_to_b(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
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
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasContextId for TestContextV1<ChainA, ChainB> {
    fn context_id(&self) -> String {
        self.context_id.clone()
    }
}

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

    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode> {
        &self.chains.node_a
    }

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode> {
        &self.chains.node_b
    }

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA> {
        &self.chains.foreign_clients.client_a_to_b
    }

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB> {
        &self.chains.foreign_clients.client_b_to_a
    }

    fn config(&self) -> &TestConfig {
        &self.config
    }

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB> {
        &self.chains
    }

    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
        &self.channel
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChannels for TestContextV2<ChainA, ChainB> {
    fn channel_a_to_b(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
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
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasContextId for TestContextV2<ChainA, ChainB> {
    fn context_id(&self) -> String {
        self.context_id.clone()
    }
}

use std::collections::HashMap;

use crate::error::handle_generic_error;
use crate::prelude::TaggedFullNodeExt;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::config::Config;
use ibc_relayer_all_in_one::extra::all_for_one::builder::CanBuildAfoFullBiRelay;
use ibc_relayer_cosmos::contexts::full::builder::CosmosRelayBuilder;
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    config: &Config,
    chains: &ConnectedChains<ChainA, ChainB>,
    packet_filter: PacketFilter,
) -> Result<impl AfoCosmosFullBiRelay, Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let runtime = chains.node_a.value().chain_driver.runtime.clone();

    let key_a = chains.node_a.wallets().value().relayer.key.clone();

    let key_b = chains.node_b.wallets().value().relayer.key.clone();

    let key_map = HashMap::from([
        (chains.chain_id_a().cloned_value(), key_a),
        (chains.chain_id_b().cloned_value(), key_b),
    ]);

    let builder = CosmosRelayBuilder::new_wrapped(
        config.clone(),
        runtime.clone(),
        Default::default(),
        packet_filter,
        Default::default(),
        key_map,
    );

    let birelay = runtime
        .block_on(builder.build_afo_full_birelay(
            chains.chain_id_a().value(),
            chains.chain_id_b().value(),
            chains.client_id_a().value(),
            chains.client_id_b().value(),
        ))
        .map_err(handle_generic_error)?;

    Ok(birelay)
}
