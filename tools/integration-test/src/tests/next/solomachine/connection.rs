use std::str::FromStr;

use ibc_relayer::config::PacketFilter;
use ibc_relayer_all_in_one::one_for_all::traits::builder::OfaBuilder;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components::relay::traits::connection::open_handshake::CanRelayConnectionOpenHandshake;
use ibc_relayer_components::relay::traits::connection::open_init::CanInitConnection;
use ibc_relayer_cosmos::types::error::Error as CosmosError;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_solomachine::context::chain::MockSolomachineChainContext;
use ibc_relayer_solomachine::context::relay::SolomachineRelay;
use ibc_relayer_solomachine::types::chain::SolomachineChainWrapper;
use ibc_test_framework::prelude::*;

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

        let solomachine_chain = solomachine_chain_context(solomachine_runtime);

        runtime
            .block_on(async move {
                let cosmos_chain = builder.builder.build_chain_a(&chain_id_a).await?;

                let solomachine_to_cosmos_relay = SolomachineRelay {
                    runtime: solomachine_chain.chain.runtime.clone(),
                    src_chain: solomachine_chain,
                    dst_chain: cosmos_chain,
                    src_client_id: ClientId::from_str("solomachine-client").unwrap(),
                    dst_client_id: ClientId::from_str("cosmos-client").unwrap(),
                };

                let relay = OfaRelayWrapper::new(solomachine_to_cosmos_relay);

                let src_connection_id = relay.init_connection(&Default::default()).await.unwrap();

                let _dst_connection_id = relay
                    .relay_connection_open_handshake(&src_connection_id)
                    .await
                    .unwrap();

                <Result<(), CosmosError>>::Ok(())
            })
            .unwrap();

        Ok(())
    }
}

pub fn solomachine_chain_context(
    runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
) -> SolomachineChainWrapper<MockSolomachineChainContext> {
    let commitment_prefix = "solomachine".to_owned();

    let chain = MockSolomachineChainContext::new(commitment_prefix, runtime);

    SolomachineChainWrapper::new(chain)
}
