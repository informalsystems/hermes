use ibc_relayer::config::{self, Config, ModeConfig};
use crate::ibc::denom::derive_ibc_denom;

use crate::prelude::*;
use crate::relayer::channel::{assert_eventually_channel_established, init_channel};
use crate::relayer::connection::{assert_eventually_connection_established, init_connection};

#[test]
fn test_supervisor() -> Result<(), Error> {
    run_binary_chain_test(&SupervisorTest)
}

struct SupervisorTest;

impl TestOverrides for SupervisorTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            clients: config::Clients {
                enabled: true,
                refresh: true,
                misbehaviour: true,
            },
            connections: config::Connections { enabled: true },
            channels: config::Channels { enabled: true },
            packets: config::Packets {
                enabled: true,
                clear_interval: 10,
                clear_on_start: true,
                filter: false,
                tx_confirmation: true,
            },
        };
    }
}

impl BinaryChainTest for SupervisorTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let (connection_id_b, _) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_b_to_a.tagged_client_id(),
            &chains.client_a_to_b.tagged_client_id(),
        )?;

        let connection_id_a = assert_eventually_connection_established(
            &chains.handle_b,
            &chains.handle_a,
            &connection_id_b.as_ref(),
        )?;

        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        let (channel_id_b, _) = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection_id_a.as_ref(),
            &connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        let channel_id_a = assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channel_id_b.as_ref(),
            &port_b.as_ref(),
        )?;

        let denom_a = chains.node_a.denom();

        let chaina_user1_balance = chains
            .node_a
            .chain_driver()
            .query_balance(&chains.node_a.wallets().user1().address(), &denom_a)?;

        let a_to_b_amount = 100;

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        chains.node_a.chain_driver().transfer_token(
            &port_a.as_ref(),
            &channel_id_a.as_ref(),
            &chains.node_a.wallets().relayer().address(),
            &chains.node_b.wallets().user1().address(),
            a_to_b_amount,
            &denom_a,
        )?;

        let denom_b = derive_ibc_denom(
            &port_b.as_ref(),
            &channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!(
            "Packet worker should still succeed and recover from account sequence mismatch error",
        );

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &chains.node_a.wallets().relayer(),
            chaina_user1_balance - a_to_b_amount,
            &denom_a,
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &chains.node_b.wallets().user1(),
            a_to_b_amount,
            &denom_b.as_ref(),
        )?;

        Ok(())
    }
}
