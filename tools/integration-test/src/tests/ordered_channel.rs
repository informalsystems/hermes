use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle, SupervisorOptions};

use crate::ibc::denom::derive_ibc_denom;
use crate::prelude::*;
use crate::util::random::random_u64_range;

#[test]
fn test_ordered_channel() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelTest)
}
pub struct OrderedChannelTest;

impl TestOverrides for OrderedChannelTest {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 0;
    }

    fn spawn_supervisor(
        &self,
        _config: &SharedConfig,
        _registry: &SharedRegistry<impl ChainHandle>,
    ) -> Result<Option<SupervisorHandle>, Error> {
        Ok(None)
    }
}

impl BinaryChannelTest for OrderedChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
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
            "Performing IBC transfer with amount {}, which should *not* be relayed",
            amount1
        );

        chains.node_a.chain_driver().transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.address(),
            &wallet_b.address(),
            amount1,
            &denom_a,
        )?;

        sleep(Duration::from_secs(2));

        let _supervisor = spawn_supervisor(
            chains.config.clone(),
            chains.registry.clone(),
            None,
            SupervisorOptions {
                health_check: false,
                force_full_scan: false,
            },
        )?;

        sleep(Duration::from_secs(2));

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

        sleep(Duration::from_secs(2));

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.as_ref(),
            balance_a - amount1 - amount2,
            &denom_a,
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.as_ref(),
            amount1 + amount2,
            &denom_b.as_ref(),
        )?;

        Ok(())
    }
}
