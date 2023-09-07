use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::relay::traits::components::auto_relayer::CanAutoRelay;
use ibc_test_framework::framework::next::chain::{HasTwoChains, HasTwoChannels};
use ibc_test_framework::ibc::denom::derive_ibc_denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;
use std::thread::sleep;

use crate::tests::next::context::build_cosmos_relay_context;

#[test]
fn test_ibc_transfer_next() -> Result<(), Error> {
    run_binary_channel_test(&IbcTransferTest)
}

pub struct IbcTransferTest;

impl TestOverrides for IbcTransferTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for IbcTransferTest {
    fn run<Context>(&self, relayer: RelayerDriver, context: &Context) -> Result<(), Error>
    where
        Context: HasTwoChains + HasTwoChannels,
    {
        let chains = context.chains();
        let channel = context.channel();
        let pf: PacketFilter = PacketFilter::default();

        let relay_context = build_cosmos_relay_context(&relayer.config, chains, pf)?;

        let runtime = chains.node_a.value().chain_driver.runtime.as_ref();

        runtime.spawn(async move {
            let _ = relay_context.auto_relay().await;
        });

        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();
        let wallet_c = chains.node_a.wallets().user2().cloned();

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_b_amount = random_u64_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!(
            "Waiting for user on chain B to receive IBC transferred amount of {} {}",
            a_to_b_amount, denom_b
        );

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_b_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount).as_ref(),
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        let balance_c = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_c.address(), &denom_a)?;

        let b_to_a_amount = random_u64_range(500, a_to_b_amount);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
            b_to_a_amount,
        );

        chains.node_b.chain_driver().ibc_transfer_token(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_c.address(),
            &denom_b.with_amount(b_to_a_amount).as_ref(),
        )?;

        info!(
            "Waiting for user on chain A to receive IBC transferred amount of {} {}",
            b_to_a_amount, denom_a
        );

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount - b_to_a_amount).as_ref(),
        )?;

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_c.address(),
            &(balance_c + b_to_a_amount).as_ref(),
        )?;

        info!(
            "successfully performed reverse IBC transfer from chain {} back to chain {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
        );

        sleep(Duration::from_secs(2));

        Ok(())
    }
}
