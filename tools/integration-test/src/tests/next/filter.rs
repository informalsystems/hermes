use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_components::relay::traits::components::packet_relayer::CanRelayPacket;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_test_framework::framework::next::chain::{HasTwoChains, HasTwoChannels};
use ibc_test_framework::ibc::denom::derive_ibc_denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

use crate::tests::next::context::build_cosmos_relay_context;

#[test]
fn test_ibc_filter_next() -> Result<(), Error> {
    run_binary_channel_test(&ChannelFilterTest)
}

pub struct ChannelFilterTest;

impl TestOverrides for ChannelFilterTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ChannelFilterTest {
    fn run<Context>(&self, relayer: RelayerDriver, context: &Context) -> Result<(), Error>
    where
        Context: HasTwoChains + HasTwoChannels,
    {
        let chains = context.chains();
        let channel = context.channel();
        let toml_content = r#"
            policy = 'deny'
            list = [
              ['transfer', 'channel-*'],
            ]
            "#;
        let pf: PacketFilter = toml::from_str(toml_content).expect("could not parse filter policy");

        let relay_context = build_cosmos_relay_context(&relayer.config, chains, pf)?;

        let runtime = chains.node_a.value().chain_driver.runtime.as_ref();

        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

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

        let packet = chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        info!("running relayer");

        runtime.block_on(async {
            relay_context
                .relay_a_to_b()
                .relay_packet(&packet)
                .await
                .unwrap()
        });

        info!("finished running relayer");

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!(
            "User on chain B should not receive the transfer of {} {}",
            a_to_b_amount, &denom_b
        );

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_b_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(0u64).as_ref(),
        )?;

        info!(
            "successfully filtered IBC transfer from chain {} to chain {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        Ok(())
    }
}
