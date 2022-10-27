use std::time::SystemTime;

use ibc_relayer_framework::base::one_for_all::traits::relay::OfaBaseRelay;
use ibc_relayer_framework::base::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use ibc_relayer_framework::base::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use ibc_test_framework::framework::base::{run_test, PrimitiveTest};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer_mock::base::types::packet::PacketKey;

use super::context::build_mock_relay_context;

#[test]
fn test_mock_chain_test() -> Result<(), Error> {
    run_test(&MockChainTest)
}

pub struct MockChainTest;

impl PrimitiveTest for MockChainTest {
    fn run(&self) -> Result<(), Error> {
        let relay_context =
            build_mock_relay_context();

        let runtime = relay_context.relay.runtime().runtime.runtime.as_ref();

        let src_client_id = relay_context.relay.src_client_id().clone();

        // Mock chains are created with height of 1, and the current height of the destination chain must be higher than the height of the packet.
        // So the packet is created with a height of 0.
        let packet = PacketKey::new(
            src_client_id,
            String::from("channel-0"),
            String::from("transfer"),
            1,
            0,
            SystemTime::now(),
        );

        info!("Relaying recv packet");

        let events =
            runtime.block_on(async { relay_context.relay_receive_packet(&0, &packet).await });

        println!("Events from relaying recv packet : {:?}", events);

        assert!(events.is_ok());

        assert!(events.as_ref().unwrap().is_some());

        let relay_ack = runtime.block_on(async {
            relay_context
                .relay_ack_packet(&1, &packet, &events.unwrap().unwrap())
                .await
        });

        assert!(relay_ack.is_ok());

        Ok(())
    }
}
