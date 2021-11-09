use core::time::Duration;
use ibc_relayer::config::{types::MaxMsgNum, Config};
use ibc_relayer::keyring::Store;
use tracing::info;

use crate::prelude::*;
use crate::relayer::transfer::tx_raw_ft_transfer;

#[test]
fn test_simulation() -> Result<(), Error> {
    run_binary_channel_test(&SimulationTest)
}

const MAX_MSGS: usize = 5;

pub struct SimulationTest;

impl TestOverrides for SimulationTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        for mut chain in config.chains.iter_mut() {
            chain.max_msg_num = MaxMsgNum(MAX_MSGS);
            chain.key_store_type = Store::Test;
        }
    }
}

impl BinaryChannelTest for SimulationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: &ConnectedChains<ChainA, ChainB>,
        channel: &ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let events = tx_raw_ft_transfer(
            chains.handle_a(),
            chains.handle_b(),
            channel,
            &chains.node_b.wallets().user1().address(),
            &chains.node_a.denom(),
            9999,
            1000,
            Duration::from_secs(0),
            MAX_MSGS,
        )?;

        info!("Performed raw TX transfer with events: {:?}", events);

        crate::suspend()
    }
}
