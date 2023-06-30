use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::relay::impls::connection::bootstrap::CanBootstrapConnection;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_test_framework::prelude::*;

use crate::tests::next::context::build_cosmos_relay_context;

#[test]
fn test_connection_handshake_next() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionHandshakeTest)
}

pub struct ConnectionHandshakeTest;

impl TestOverrides for ConnectionHandshakeTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for ConnectionHandshakeTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let pf: PacketFilter = PacketFilter::default();

        let runtime = chains.node_a.value().chain_driver.runtime.as_ref();

        let relay_context = build_cosmos_relay_context(&relayer.config, &chains, pf)?;

        let (connection_id_a, connection_id_b) = runtime
            .block_on(async move {
                relay_context
                    .relay_a_to_b()
                    .bootstrap_connection(&Default::default())
                    .await
            })
            .unwrap();

        info!(
            "bootstrapped new IBC connections with ID {} and {}",
            connection_id_a, connection_id_b
        );

        Ok(())
    }
}
