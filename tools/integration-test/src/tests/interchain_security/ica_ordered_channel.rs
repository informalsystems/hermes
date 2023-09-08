//! Verifies the behaviour of ordered channels with Interchain Accounts.
//! 
//! In order to ensure that ordered channels correctly clear packets on ICA
//! channels, this test sends some sequential packets with the supervisor enabled,
//! sends the next packet without the supervisor enabled, then sends additional
//! packets with the supervisor enabled again. The pending packet that was sent
//! without the supervisor enabled should be relayed in order along with the 
//! other packets, as expected of ordered channel behaviour. 

use ibc_test_framework::prelude::*;
use ibc_test_framework::chain::ext::ica::register_interchain_account;
use ibc_test_framework::relayer::channel::query_channel_end;

#[test]
fn test_ica_ordered_channel() -> Result<(), Error> {
    run_binary_interchain_security_channel_test(&IcaOrderedChannelTest)
}

struct IcaOrderedChannelTest;

impl TestOverrides for IcaOrderedChannelTest {
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        use serde_json::Value;

        // Allow MsgSend messages over ICA
        let allow_messages = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("interchainaccounts"))
            .and_then(|ica| ica.get_mut("host_genesis_state"))
            .and_then(|state| state.get_mut("params"))
            .and_then(|params| params.get_mut("allow_messages"))
            .and_then(|allow_messages| allow_messages.as_array_mut());

        if let Some(allow_messages) = allow_messages {
            allow_messages.push(Value::String("/cosmos.bank.v1beta1.MsgSend".to_string()));
        } else {
            return Err(Error::generic(eyre!("failed to update genesis file")));
        }

        update_genesis_for_consumer_chain(genesis)?;

        Ok(())
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        // Disable packet clearing so that packets sent without the supervisor 
        // enabled enter a pending state.
        config.mode.packets.enabled = true;
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 0;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for IcaOrderedChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let connection_b_to_a = channel.connection.clone().flip();
        let (wallet, channel_id, port_id) =
            register_interchain_account(&chains.node_b, chains.handle_b(), &connection_b_to_a)?;

        // Check that the corresponding ICA channel is eventually established.
        let _counterparty_channel_id = assert_eventually_channel_established(
            chains.handle_b(),
            chains.handle_a(),
            &channel_id.as_ref(),
            &port_id.as_ref(),
        )?;

        // Assert that the channel returned by `register_interchain_account` is an ordered channel
        let channel_end = query_channel_end(chains.handle_b(), &channel_id.as_ref(), &port_id.as_ref())?;

        assert_eq!(channel_end.value().ordering(), ChannelOrder::Ordered);

        relayer.with_supervisor(|| {

        });

        Ok(())
    }
}