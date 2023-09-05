use alloc::string::String;
use ibc_relayer_components::chain::traits::queries::write_ack::CanQueryWriteAcknowledgement;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use std::time::Duration;

use ibc_relayer_components::relay::traits::components::packet_relayer::CanRelayPacket;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use tracing::info;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::base::types::events::Event;
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::tests::util::context::build_mock_relay_context;

#[tokio::test]
async fn test_mock_chain_relay() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let source_client_id = relay_context.src_client_id().clone();
    let destination_client_id = relay_context.dst_client_id().clone();

    src_chain.map_channel_to_client(src_channel_id.clone(), source_client_id);
    dst_chain.map_channel_to_client(dst_channel_id.clone(), destination_client_id);

    let packet = src_chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(10),
        MockTimestamp(60000),
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.get_current_state();

        assert!(
            !state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet already received on destination chain before relaying it"
        );
    }

    let height = src_chain.get_current_height();

    // Chain submits the transaction to be relayed
    src_chain.send_packet(height, packet.clone())?;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.get_current_state();

        assert!(
            state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet not received on destination chain"
        );
    }

    {
        info!("Check that the acknowledgment has been received by the source chain");

        let state = src_chain.get_current_state();

        assert!(
            state.check_acknowledged((packet.src_port_id, packet.src_channel_id, packet.sequence)),
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

    let source_client_id = relay_context.src_client_id().clone();
    let destination_client_id = relay_context.dst_client_id().clone();

    src_chain.map_channel_to_client(src_channel_id.clone(), source_client_id);
    dst_chain.map_channel_to_client(dst_channel_id.clone(), destination_client_id);

    let packet = src_chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(10),
        MockTimestamp(60000),
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.get_current_state();

        assert!(
            !state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet already received on destination chain before relaying it"
        );
    }

    let src_height = src_chain.get_current_height();
    let runtime = &relay_context.runtime;

    src_chain.send_packet(src_height, packet.clone())?;

    // Sleep enough to trigger timeout from timestamp timeout
    runtime.sleep(Duration::from_millis(70000)).await;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has not been received by the destination chain");

        let state = dst_chain.get_current_state();

        assert!(
            !state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet received on destination chain, but should have timed out"
        );
    }

    {
        info!("Check that the timeout packet been received by the source chain");

        let state = src_chain.get_current_state();
        let elapsed_time = runtime.get_time();

        assert!(
            state.check_timeout(packet, src_height, elapsed_time),
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

    let source_client_id = relay_context.src_client_id().clone();
    let destination_client_id = relay_context.dst_client_id().clone();

    src_chain.map_channel_to_client(src_channel_id.clone(), source_client_id);
    dst_chain.map_channel_to_client(dst_channel_id.clone(), destination_client_id);

    let packet = src_chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(3),
        MockTimestamp(60000),
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.get_current_state();

        assert!(
            !state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet already received on destination chain before relaying it"
        );
    }

    let src_height = src_chain.get_current_height();

    src_chain.send_packet(src_height, packet.clone())?;

    // Increase height of destination chain to trigger Height timeout
    for _ in 0..3 {
        dst_chain.new_block()?;
    }

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.get_current_state();

        assert!(
            !state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet received on destination chain, but should have timed out"
        );
    }

    {
        info!("Check that the timeout packet has been received by the source chain");

        let state = src_chain.get_current_state();
        let dst_height = dst_chain.get_current_height();
        let runtime = &relay_context.runtime;
        let elapsed_time = runtime.get_time();

        assert!(
            state.check_timeout(packet, dst_height, elapsed_time),
            "Packet should be registered as timed out"
        );
    }

    Ok(())
}

#[tokio::test]
async fn test_mock_chain_query_write_ack() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let source_client_id = relay_context.src_client_id().clone();
    let src_port_id = String::from("transfer");
    let destination_client_id = relay_context.dst_client_id().clone();
    let dst_port_id = String::from("transfer");

    src_chain.map_channel_to_client(src_channel_id.clone(), source_client_id);
    dst_chain.map_channel_to_client(dst_channel_id.clone(), destination_client_id);

    let packet = src_chain.build_send_packet(
        src_channel_id.clone(),
        src_port_id.clone(),
        dst_channel_id.clone(),
        dst_port_id.clone(),
        1,
        MockHeight(10),
        MockTimestamp(60000),
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.get_current_state();

        assert!(
            !state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet already received on destination chain before relaying it"
        );

        info!("Check that no WriteAcknowledgmentEvent is returned by query_write_ack");

        let write_ack = dst_chain.query_write_acknowledgement_event(&packet).await;
        assert!(
            write_ack.is_ok(),
            "query_write_acknowledgement_event returned an error"
        );
        assert!(
            write_ack.unwrap().is_none(),
            "WriteAcknowlegmentEvent should be None as the chain hasn't received the packet yet"
        );
    }

    let height = src_chain.get_current_height();

    src_chain.send_packet(height, packet.clone())?;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.get_current_state();

        assert!(
            state.check_received((
                packet.dst_port_id.clone(),
                packet.dst_channel_id.clone(),
                packet.sequence
            )),
            "Packet not received on destination chain"
        );

        info!("Check that a WriteAcknowledgmentEvent is returned by query_write_ack");

        let write_ack = dst_chain.query_write_acknowledgement_event(&packet).await;
        assert!(
            write_ack.is_ok(),
            "query_write_acknowledgement_event returned an error"
        );
        assert!(write_ack.unwrap().is_some(), "A WriteAcknowlegmentEvent should be returned by query_write_acknowledgement_event since the chain received the packet");
    }

    {
        info!("Check that the acknowledgment has been received by the source chain");

        let state = src_chain.get_current_state();

        assert!(
            state.check_acknowledged((packet.src_port_id, packet.src_channel_id, packet.sequence)),
            "Acknowledgment not found on source chain"
        );
    }

    Ok(())
}

#[tokio::test]
async fn test_mock_chain_process_update_client_message() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let source_client_id = relay_context.src_client_id().clone();
    let destination_client_id = relay_context.dst_client_id().clone();

    src_chain.map_channel_to_client(src_channel_id, source_client_id.clone());
    dst_chain.map_channel_to_client(dst_channel_id, destination_client_id);

    let src_height = src_chain.get_current_height();
    let src_state = src_chain.get_current_state();

    let update_client_message = vec![MockMessage::UpdateClient(
        source_client_id.clone(),
        src_height,
        src_state,
    )];

    info!("Check that no consensus states have been added");

    let src_consensus_state =
        src_chain.query_consensus_state_at_height(source_client_id.clone(), src_height);

    assert!(
        src_consensus_state.is_err(),
        "Found a consensus state where there should have been none."
    );

    let events = src_chain.process_messages(update_client_message)?;

    assert_eq!(
        events,
        vec![vec![]],
        "Found an Event where there should have been none."
    );

    let src_consensus_state =
        src_chain.query_consensus_state_at_height(source_client_id, src_height);

    assert!(
        src_consensus_state.is_ok(),
        "Expected a consensus state, but found none."
    );

    Ok(())
}

#[tokio::test]
async fn test_mock_chain_process_recv_packet() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_channel_id = "channel-0".to_owned();
    let dst_channel_id = "channel-1".to_owned();

    let source_client_id = relay_context.src_client_id().clone();
    let destination_client_id = relay_context.dst_client_id().clone();

    src_chain.map_channel_to_client(dst_channel_id.clone(), source_client_id.clone());
    dst_chain.map_channel_to_client(dst_channel_id.clone(), destination_client_id);

    let packet = src_chain.build_send_packet(
        src_channel_id,
        String::from("transfer"),
        dst_channel_id,
        String::from("transfer"),
        1,
        MockHeight(10),
        MockTimestamp(60000),
    );

    let src_height = src_chain.get_current_height();

    src_chain.send_packet(src_height, packet.clone())?;

    let src_state = src_chain.get_current_state();

    let recv_packet_message = vec![
        MockMessage::UpdateClient(source_client_id, src_height.increment(), src_state),
        MockMessage::RecvPacket(src_height, packet),
    ];

    let events = src_chain.process_messages(recv_packet_message)?;

    assert_eq!(
        events.len(),
        2,
        "Expected `process_messages` to return 2 events"
    );
    assert_eq!(
        events.first(),
        Some(&vec![]),
        "Expected first event returned from processing UpdateClient message to be empty"
    );
    assert_eq!(
        events.last(),
        Some(&vec![Event::WriteAcknowledgment(src_height)]),
        "Expected last event return from processing RecvPacket message to contain a WriteAcknowledgment"
    );

    Ok(())
}
