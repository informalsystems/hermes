use alloc::string::String;
use tracing::info;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::tests::util::context::build_mock_relay_context;
use ibc_relayer_framework::base::one_for_all::traits::relay::OfaBaseRelay;
use ibc_relayer_framework::base::relay::traits::packet_relayer::CanRelayPacket;

#[tokio::test]
async fn test_mock_chain_test() -> Result<(), Error> {
    let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

    let src_client_id = relay_context.relay.src_client_id().clone();

    let packet = src_chain.chain.build_send_packet(
        src_client_id,
        String::from("channel-0"),
        String::from("transfer"),
        MockHeight(10),
        MockHeight(10),
    );

    {
        info!("Check that the packet has not yet been received");

        let state = dst_chain.chain.get_current_state();

        assert!(!state.check_received(&packet.port_id, &packet.channel_id, &packet.sequence), "Packet already received on destination chain before relaying it");
    }

    src_chain.chain.send_packet(packet.clone())?;

    src_chain.chain.new_block()?;

    let events = relay_context.relay_packet(&packet).await;

    assert!(events.is_ok(), "{}", events.err().unwrap());

    {
        info!("Check that the packet has been received by the destination chain");

        let state = dst_chain.chain.get_current_state();

        assert!(state.check_received(&packet.port_id, &packet.channel_id, &packet.sequence), "Packet not received on destination chain");
    }

    {
        info!("Check that the acknowledgment has been received by the source chain");

        let state = src_chain.chain.get_current_state();

        assert!(state.check_acknowledged(packet.port_id, packet.channel_id, packet.sequence), "Acknowledgment not found on source chain");
    }

    Ok(())
}
