use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::cosmos::client::Settings;
use ibc_relayer::channel::version::Version;
use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::builder::impls::bootstrap::birelay::CanBootstrapBiRelay;
use ibc_relayer_components::relay::impls::channel::bootstrap::CanBootstrapChannel;
use ibc_relayer_components::relay::impls::connection::bootstrap::CanBootstrapConnection;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_cosmos::types::channel::CosmosInitChannelOptions;
use ibc_relayer_cosmos::types::error::Error as CosmosError;

#[tokio::test]
async fn connection_handshake() -> Result<(), Error> {

    let runtime = todo!();

    runtime
        .block_on(async move {
            let birelay = todo!();

            let (connection_id_a, connection_id_b) = birelay
                .relay_a_to_b()
                .bootstrap_connection(&Default::default())
                .await?;

            info!(
                "bootstrapped new IBC connections with ID {} and {}",
                connection_id_a, connection_id_b
            );

            let channel_init_options = CosmosInitChannelOptions {
                ordering: Ordering::Unordered,
                connection_hops: vec![connection_id_a],
                channel_version: Version::ics20(),
            };

            let (channel_id_a, channel_id_b) = birelay
                .relay_a_to_b()
                .bootstrap_channel(
                    &PortId::transfer(),
                    &PortId::transfer(),
                    &channel_init_options,
                )
                .await?;

            info!(
                "bootstrapped new IBC channel with ID {} and {}",
                channel_id_a, channel_id_b
            );

            <Result<(), CosmosError>>::Ok(())
        })
        .unwrap();

    Ok(())
}