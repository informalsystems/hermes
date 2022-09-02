use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::transfer::build_transfer_message;

#[test]
fn test_events() -> Result<(), Error> {
    run_binary_channel_test(&EventsTest)
}

pub struct EventsTest;

impl TestOverrides for EventsTest {}

impl BinaryChannelTest for EventsTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let transfer_message = build_transfer_message(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a,
            100,
            None,
        )?;

        let messages = vec![transfer_message; 2];

        let events = chains
            .node_a
            .chain_driver()
            .send_tx(&wallet_a.as_ref(), messages)?;

        info!("IBC send TX events: {:#?}", events);

        Ok(())
    }
}
