use ibc_relayer_framework::base::one_for_all::traits::relay::OfaBaseRelay;
use ibc_relayer_framework::base::relay::traits::packet_relayer::CanRelayPacket;
use ibc_test_framework::framework::base::{run_test, PrimitiveTest};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer_mock::base::types::height::Height;
use ibc_test_framework::relayer_mock::base::types::packet::PacketKey;

use super::context::build_mock_relay_context;

#[test]
fn test_mock_chain_test() -> Result<(), Error> {
    run_test(&MockChainTest)
}

pub struct MockChainTest;

impl PrimitiveTest for MockChainTest {
    fn run(&self) -> Result<(), Error> {
        let (relay_context, src_chain, dst_chain) = build_mock_relay_context();

        let runtime = relay_context.relay.runtime().runtime.runtime.as_ref();

        let src_client_id = relay_context.relay.src_client_id().clone();

        let packet = PacketKey::new(
            src_client_id,
            String::from("channel-0"),
            String::from("transfer"),
            1,
            Height(10),
            Height(10),
        );

        {
            info!("Check that the packet has not yet been received");

            let l_h = dst_chain.chain.get_latest_height();

            assert!(l_h.is_some());

            let state = dst_chain.chain.query_state(l_h.unwrap());

            assert!(state.is_some());

            assert!(!state.unwrap().check_received(
                &packet.port_id,
                &packet.channel_id,
                &packet.sequence
            ));
        }

        // Source chain must be higher than destination chain
        src_chain.chain.new_block();

        let events = runtime.block_on(async { relay_context.relay_packet(&packet).await });

        assert!(events.is_ok());

        {
            info!("Check that the packet has been received by the destination chain");

            let l_h = dst_chain.chain.get_latest_height();

            assert!(l_h.is_some());

            let state = dst_chain.chain.query_state(l_h.unwrap());

            assert!(state.is_some());

            assert!(state.unwrap().check_received(
                &packet.port_id,
                &packet.channel_id,
                &packet.sequence
            ));
        }

        {
            info!("Check that the acknowledgment has been received by the source chain");

            let l_h = src_chain.chain.get_latest_height();

            assert!(l_h.is_some());

            let state = src_chain.chain.query_state(l_h.unwrap());

            assert!(state.is_some());

            assert!(state.unwrap().check_acknowledged(
                packet.port_id,
                packet.channel_id,
                packet.sequence
            ));
        }

        Ok(())
    }
}
