use std::thread;

use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::cosmos::client::Settings;
use ibc_relayer::config::PacketFilter;
use ibc_relayer_all_in_one::one_for_all::traits::builder::OfaBuilder;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_components::relay::traits::connection::open_handshake::CanRelayConnectionOpenHandshake;
use ibc_relayer_components::relay::traits::connection::open_init::CanInitConnection;
use ibc_relayer_components::relay::traits::create_client::CanCreateClient;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components_extra::batch::worker::CanSpawnBatchMessageWorker;
use ibc_relayer_cosmos::types::error::Error as CosmosError;
use ibc_relayer_cosmos::types::telemetry::CosmosTelemetry;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_solomachine::context::chain::MockSolomachineChainContext;
use ibc_relayer_solomachine::context::relay::SolomachineRelay;
use ibc_relayer_solomachine::types::batch::{CosmosBatchPayload, SolomachineBatchPayload};
use ibc_relayer_solomachine::types::chain::SolomachineChainWrapper;
use ibc_test_framework::prelude::*;
use tokio::sync::mpsc;

use crate::tests::next::context::new_cosmos_builder;

#[test]
fn test_solomachine_to_cosmos_next() -> Result<(), Error> {
    run_binary_chain_test(&SolomachineToCosmosTest)
}

pub struct SolomachineToCosmosTest;

impl TestOverrides for SolomachineToCosmosTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for SolomachineToCosmosTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let pf: PacketFilter = PacketFilter::default();

        let runtime = chains.node_a.value().chain_driver.runtime.as_ref();

        let builder = new_cosmos_builder(&relayer.config, &chains, pf)?;

        let chain_id_a = chains.chain_id_a().cloned_value();

        let solomachine_runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(
            chains.node_b.value().chain_driver.runtime.clone(),
        ));

        let solomachine_chain = solomachine_chain_context(solomachine_runtime, Default::default());

        let client_settings = ClientSettings::Tendermint(Settings {
            max_clock_drift: Duration::from_secs(40),
            trust_threshold: Default::default(),
            trusting_period: None,
        });

        runtime
            .block_on(async move {
                let cosmos_chain = builder.builder.build_chain_a(&chain_id_a).await?;
                let wrapped_solomachine_chain = OfaChainWrapper::new(solomachine_chain.clone());
                let wrapped_cosmos_chain = OfaChainWrapper::new(cosmos_chain.clone());

                let src_client_id = OfaRelayWrapper::<SolomachineRelay>::create_client(
                    SourceTarget,
                    &wrapped_solomachine_chain,
                    &wrapped_cosmos_chain,
                    &client_settings,
                )
                .await
                .unwrap();

                let dst_client_id = OfaRelayWrapper::<SolomachineRelay>::create_client(
                    DestinationTarget,
                    &wrapped_cosmos_chain,
                    &wrapped_solomachine_chain,
                    &(),
                )
                .await
                .unwrap();

                info!("src_client_id: {src_client_id:#?}");
                info!("dst_client_id: {dst_client_id:#?}");

                thread::sleep(Duration::from_secs(2));
                let (_src_sender, src_recv) = mpsc::unbounded_channel::<SolomachineBatchPayload>();
                let (dst_sender, dst_recv) = mpsc::unbounded_channel::<CosmosBatchPayload>();

                let solomachine_to_cosmos_relay = SolomachineRelay {
                    runtime: solomachine_chain.chain.runtime.clone(),
                    src_chain: wrapped_solomachine_chain,
                    dst_chain: wrapped_cosmos_chain,
                    src_client_id,
                    dst_client_id,
                    //src_chain_message_batch_sender: src_sender,
                    dst_chain_message_batch_sender: dst_sender,
                };

                let relay = OfaRelayWrapper::new(solomachine_to_cosmos_relay);

                relay.clone().spawn_batch_message_worker(
                    SourceTarget,
                    Default::default(),
                    src_recv,
                );

                relay.clone().spawn_batch_message_worker(
                    DestinationTarget,
                    Default::default(),
                    dst_recv,
                );

                let src_connection_id = relay.init_connection(&Default::default()).await.unwrap();

                info!("src_connection_id: {src_connection_id:#?}");

                let dst_connection_id = relay
                    .relay_connection_open_handshake(&src_connection_id)
                    .await
                    .unwrap();

                info!("dst_connection_id: {dst_connection_id:#?}");

                <Result<(), CosmosError>>::Ok(())
            })
            .unwrap();

        Ok(())
    }
}

pub fn solomachine_chain_context(
    runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    telemetry: CosmosTelemetry,
) -> SolomachineChainWrapper<MockSolomachineChainContext> {
    let wrapped_telemetry = OfaTelemetryWrapper::new(telemetry);
    let commitment_prefix = "solomachine".to_owned();

    let chain = MockSolomachineChainContext::new(
        "solomachine1",
        commitment_prefix,
        runtime,
        wrapped_telemetry,
    );

    SolomachineChainWrapper::new(chain)
}
