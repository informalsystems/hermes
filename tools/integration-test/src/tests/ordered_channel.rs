use ibc_relayer::keyring::Store;
use ibc_test_framework::ibc::denom::derive_ibc_denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

const TRANSFER_COUNT: u64 = 10;

#[test]
fn test_ordered_channel() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelTest)
}

pub struct OrderedChannelTest;

impl TestOverrides for OrderedChannelTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        // Disabling clear_on_start should make the relayer not
        // relay any packet it missed before starting.
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 0;

        for mut chain in config.chains.iter_mut() {
            // We currently need the Test key store type to persist the keys
            // across relayer driver forks.
            chain.key_store_type = Store::Test;
        }
    }

    fn channel_order(&self) -> Order {
        Order::Ordered
    }
}

impl BinaryChannelTest for OrderedChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let amount1 = random_u64_range(1000, 5000);

        info!(
            "Performing IBC transfer with amount {} times {}, which should be relayed because its an ordered channel",
            amount1, TRANSFER_COUNT
        );

        for _ in 0..TRANSFER_COUNT {
            chains.node_a.chain_driver().transfer_token(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &wallet_a.address(),
                &wallet_b.address(),
                amount1,
                &denom_a,
            )?;

            // Have to sleep 1 second to wait for the transfer to be
            // committed before doing another one.
            std::thread::sleep(Duration::from_secs(1));
        }

        // Fork the relayer driver with different keys, so that we can spawn
        // two racing relayers.
        let relayer2 = {
            let chain_id_a = chains.node_a.chain_id().into_value();
            let chain_id_b = chains.node_b.chain_id().into_value();
            let relayer_wallet_a = chains.node_a.wallets().relayer2().id().cloned_value().0;
            let relayer_wallet_b = chains.node_b.wallets().relayer2().id().cloned_value().0;

            relayer.fork(|config| {
                for mut chain in config.chains.iter_mut() {
                    if &chain.id == chain_id_a {
                        chain.key_name = relayer_wallet_a.clone();
                    } else if &chain.id == chain_id_b {
                        chain.key_name = relayer_wallet_b.clone();
                    }
                }
            })
        };

        let _relayer1 = relayer.spawn_supervisor()?;
        let _relayer2 = relayer2.spawn_supervisor()?;

        sleep(Duration::from_secs(3));

        let amount2 = random_u64_range(1000, 5000);

        info!(
            "Performing IBC transfer with amount {}, which should be relayed",
            amount2
        );

        chains.node_a.chain_driver().transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.address(),
            &wallet_b.address(),
            amount2,
            &denom_a,
        )?;

        sleep(Duration::from_secs(1));

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        // Wallet on chain A should have both amount deducted.
        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            balance_a - (amount1 * TRANSFER_COUNT) - amount2,
            &denom_a,
        )?;

        // Wallet on chain B should receive both IBC transfers
        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            (amount1 * TRANSFER_COUNT) + amount2,
            &denom_b.as_ref(),
        )?;

        Ok(())
    }
}
