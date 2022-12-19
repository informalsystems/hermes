use alloc::string::String;
use ibc_relayer_framework::base::runtime::traits::sleep::CanSleep;
use std::time::Duration;
use tracing::info;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::tests::util::context::build_mock_relay_context;

use ibc_relayer_framework::base::one_for_all::traits::relay::OfaBaseRelay;
use ibc_relayer_framework::base::relay::traits::packet_relayer::CanRelayPacket;

// FIXME: Fix the mock chain building of receive packet message
// #[tokio::test]
#[allow(dead_code)]
async fn test_mock_chain_relay() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let src_client_id = relay_context.relay.src_client_id().clone();
    let dst_client_id = relay_context.relay.dst_client_id().clone();

    src_chain
        .chain
        .map_channel_to_client(src_channel_id.clone(), src_client_id);
    dst_chain
        .chain
        .map_channel_to_client(dst_channel_id.clone(), dst_client_id);

    let packet = src_chain.chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(10),
        60000,
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.chain.get_current_state();

        assert!(
            !state.check_received(
                &packet.dst_port_id,
                &packet.dst_channel_id,
                &packet.sequence
            ),
            "Packet already received on destination chain before relaying it"
        );
    }

    src_chain.chain.send_packet(packet.clone())?;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.chain.get_current_state();

        assert!(
            state.check_received(
                &packet.dst_port_id,
                &packet.dst_channel_id,
                &packet.sequence
            ),
            "Packet not received on destination chain"
        );
    }

    {
        info!("Check that the acknowledgment has been received by the source chain");

        let state = src_chain.chain.get_current_state();

        assert!(
            state.check_acknowledged(packet.src_port_id, packet.src_channel_id, packet.sequence),
            "Acknowledgment not found on source chain"
        );
    }

    Ok(())
}

#[tokio::test]
async fn test_mock_chain_timeout_timestamp() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let src_client_id = relay_context.relay.src_client_id().clone();
    let dst_client_id = relay_context.relay.dst_client_id().clone();

    src_chain
        .chain
        .map_channel_to_client(src_channel_id.clone(), src_client_id);
    dst_chain
        .chain
        .map_channel_to_client(dst_channel_id.clone(), dst_client_id);

    let packet = src_chain.chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(10),
        60000,
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.chain.get_current_state();

        assert!(
            !state.check_received(
                &packet.dst_port_id,
                &packet.dst_channel_id,
                &packet.sequence
            ),
            "Packet already received on destination chain before relaying it"
        );
    }

    src_chain.chain.send_packet(packet.clone())?;

    // Sleep enough to trigger timeout from timestamp timeout
    relay_context
        .relay
        .runtime()
        .sleep(Duration::from_millis(70000))
        .await;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.chain.get_current_state();

        assert!(
            !state.check_received(
                &packet.dst_port_id,
                &packet.dst_channel_id,
                &packet.sequence
            ),
            "Packet received on destination chain, but should have timed out"
        );
    }

    {
        info!("Check that the acknowledgment has been received by the source chain");

        let state = src_chain.chain.get_current_state();

        assert!(
            state.check_timeout(packet.src_port_id, packet.src_channel_id, packet.sequence),
            "Packet should be registered as timed out"
        );
    }
    Ok(())
}

#[tokio::test]
async fn test_mock_chain_timeout_height() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let src_client_id = relay_context.relay.src_client_id().clone();
    let dst_client_id = relay_context.relay.dst_client_id().clone();

    src_chain
        .chain
        .map_channel_to_client(src_channel_id.clone(), src_client_id);
    dst_chain
        .chain
        .map_channel_to_client(dst_channel_id.clone(), dst_client_id);

    let packet = src_chain.chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(3),
        60000,
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.chain.get_current_state();

        assert!(
            !state.check_received(
                &packet.dst_port_id,
                &packet.dst_channel_id,
                &packet.sequence
            ),
            "Packet already received on destination chain before relaying it"
        );
    }

    src_chain.chain.send_packet(packet.clone())?;

    // Increase height of destination chain to trigger Height timeout
    dst_chain.chain.new_block()?;
    dst_chain.chain.new_block()?;
    dst_chain.chain.new_block()?;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.chain.get_current_state();

        assert!(
            !state.check_received(
                &packet.dst_port_id,
                &packet.dst_channel_id,
                &packet.sequence
            ),
            "Packet received on destination chain, but should have timed out"
        );
    }

    {
        info!("Check that the acknowledgment has been received by the source chain");

        let state = src_chain.chain.get_current_state();

        assert!(
            state.check_timeout(packet.src_port_id, packet.src_channel_id, packet.sequence),
            "Packet should be registered as timed out"
        );
    }
    Ok(())
}
