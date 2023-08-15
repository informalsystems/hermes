use ibc_relayer_components::relay::traits::connection::open_handshake::CanRelayConnectionOpenHandshake;
use ibc_relayer_components::relay::traits::connection::open_init::CanInitConnection;

use crate::tests::utils::context::solomachine_to_cosmos_relay_context;
use crate::types::error::Error;

/*#[tokio::test]
async fn connection_handshake() -> Result<(), Error> {

    let runtime = todo!();

    runtime
        .block_on(async move {
            let birelay = solomachine_birelay_context();

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
}*/

#[tokio::test]
async fn single_step_connection_handshake() -> Result<(), Error> {
    let relay_context = solomachine_to_cosmos_relay_context();

    let src_connection_id = relay_context
        .init_connection(&Default::default())
        .await
        .unwrap();

    let _dst_connection_id = relay_context
        .relay_connection_open_handshake(&src_connection_id)
        .await
        .unwrap();

    Ok(())
}
