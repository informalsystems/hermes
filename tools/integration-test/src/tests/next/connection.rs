use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::cosmos::client::Settings;
use ibc_relayer::channel::version::Version;
use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::builder::impls::bootstrap::birelay::CanBootstrapBiRelay;
use ibc_relayer_components::relay::impls::channel::bootstrap::CanBootstrapChannel;
use ibc_relayer_components::relay::impls::connection::bootstrap::CanBootstrapConnection;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_cosmos::types::channel::CosmosInitChannelOptions;
use ibc_test_framework::prelude::*;

use crate::tests::next::context::new_cosmos_builder;

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

        let builder = new_cosmos_builder(&relayer.config, &chains, pf)?;

        let chain_id_a = chains.chain_id_a().cloned_value();
        let chain_id_b = chains.chain_id_b().cloned_value();

        // TODO: figure ways to build client settings easily without too much dependencies
        let client_settings = ClientSettings::Tendermint(Settings {
            max_clock_drift: Duration::from_secs(40),
            trust_threshold: Default::default(),
            trusting_period: None,
        });

        let (connection_id_a, connection_id_b) = runtime
            .block_on(async move {
                let birelay = builder
                    .bootstrap_birelay(&chain_id_a, &chain_id_b, &client_settings, &client_settings)
                    .await?;

                let (src_connection_id, _dst_connection_id) = birelay
                    .relay_a_to_b()
                    .bootstrap_connection(&Default::default())
                    .await?;

                let channel_init_options = CosmosInitChannelOptions {
                    ordering: Ordering::Unordered,
                    connection_hops: vec![src_connection_id],
                    channel_version: Version::ics20(),
                };

                birelay
                    .relay_a_to_b()
                    .bootstrap_channel(
                        &PortId::transfer(),
                        &PortId::transfer(),
                        &channel_init_options,
                    )
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
