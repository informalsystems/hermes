//! Verifies the behaviour of ordered channels with Interchain Accounts.
//!
//! In order to ensure that ordered channels correctly clear packets on ICA
//! channels, this test sends some sequential packets with the supervisor enabled,
//! sends the next packet *without* the supervisor enabled, then sends additional
//! packets with the supervisor enabled again. The pending packet that was sent
//! without the supervisor enabled should be relayed in order along with the
//! other packets, as expected of ordered channel behaviour.

use std::str::FromStr;

use ibc_relayer_types::applications::ics27_ica::cosmos_tx::CosmosTx;
use ibc_relayer_types::applications::ics27_ica::packet_data::InterchainAccountPacketData;
use ibc_relayer_types::applications::transfer::msgs::send::MsgSend;
use ibc_relayer_types::applications::transfer::{Amount, Coin};
use ibc_relayer_types::bigint::U256;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_test_framework::chain::ext::ica::register_interchain_account;
use ibc_test_framework::framework::binary::channel::run_binary_interchain_security_channel_test;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::assert_eventually_channel_established;
use ibc_test_framework::relayer::channel::query_channel_end;
use ibc_test_framework::util::interchain_security::{
    interchain_send_tx, update_genesis_for_consumer_chain, update_relayer_config_for_consumer_chain,
};

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
        config.mode.clients.misbehaviour = false;

        config.mode.channels.enabled = true;

        // Disable packet clearing so that packets sent without the supervisor
        // enabled enter a pending state.
        config.mode.packets.enabled = true;
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 0;
        // This is needed for ordered channels
        config.mode.packets.force_disable_clear_on_start = true;

        update_relayer_config_for_consumer_chain(config);
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

        relayer.with_supervisor(|| {
            // Check that the corresponding ICA channel is eventually established.
            let _counterparty_channel_id = assert_eventually_channel_established(
                chains.handle_b(),
                chains.handle_a(),
                &channel_id.as_ref(),
                &port_id.as_ref(),
            )?;

            Ok(())
        })?;

        // Assert that the channel returned by `register_interchain_account` is an ordered channel
        let channel_end =
            query_channel_end(chains.handle_b(), &channel_id.as_ref(), &port_id.as_ref())?;

        assert_eq!(channel_end.value().ordering(), &Ordering::Ordered);

        // Query the controller chain for the address of the ICA wallet on the host chain.
        let ica_address = chains.node_b.chain_driver().query_interchain_account(
            &wallet.address(),
            &channel.connection.connection_id_b.as_ref(),
        )?;

        let stake_denom: MonoTagged<ChainA, Denom> = MonoTagged::new(Denom::base("stake"));

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(0u64).as_ref(),
        )?;

        // Send funds to the interchain account.
        let ica_fund = 42000u64;

        chains.node_a.chain_driver().local_transfer_token(
            &chains.node_a.wallets().user1(),
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund).as_ref(),
        )?;

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund).as_ref(),
        )?;

        let amount = 1200;

        let msg = MsgSend {
            from_address: ica_address.to_string(),
            to_address: chains.node_a.wallets().user2().address().to_string(),
            amount: vec![Coin {
                denom: stake_denom.to_string(),
                amount: Amount(U256::from(amount)),
            }],
        };

        let raw_msg = msg.to_any();

        let cosmos_tx = CosmosTx {
            messages: vec![raw_msg],
        };

        let raw_cosmos_tx = cosmos_tx.to_any();

        let interchain_account_packet_data = InterchainAccountPacketData::new(raw_cosmos_tx.value);

        let signer = Signer::from_str(&wallet.address().to_string()).unwrap();

        let user2_balance = chains.node_a.chain_driver().query_balance(
            &chains.node_a.wallets().user2().address(),
            &stake_denom.as_ref(),
        )?;

        relayer.with_supervisor(|| {
            let ica_events = interchain_send_tx(
                chains.handle_b(),
                &signer,
                &channel.connection.connection_id_b.0,
                interchain_account_packet_data.clone(),
                Timestamp::from_nanoseconds(120000000000).unwrap(),
            )?;

            // Check that the ICA account's balance has been debited the sent amount.
            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &ica_address.as_ref(),
                &stake_denom.with_amount(ica_fund - amount).as_ref(),
            )?;

            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &chains.node_a.wallets().user2().address(),
                &(user2_balance.clone() + amount).as_ref(),
            )?;

            info!("First ICA transfer made with supervisor: {ica_events:#?}");

            Ok(())
        })?;

        let ica_events = interchain_send_tx(
            chains.handle_b(),
            &signer,
            &channel.connection.connection_id_b.0,
            interchain_account_packet_data.clone(),
            Timestamp::from_nanoseconds(120000000000).unwrap(),
        )?;

        info!("Second ICA transfer made without supervisor: {ica_events:#?}");

        relayer.with_supervisor(|| {
            let ica_events = interchain_send_tx(
                chains.handle_b(),
                &signer,
                &channel.connection.connection_id_b.0,
                interchain_account_packet_data,
                Timestamp::from_nanoseconds(120000000000).unwrap(),
            )?;

            // Check that the ICA account's balance has been debited the sent amount.
            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &ica_address.as_ref(),
                &stake_denom.with_amount(ica_fund - 3 * amount).as_ref(),
            )?;

            info!("Third ICA transfer made with supervisor: {ica_events:#?}");

            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &chains.node_a.wallets().user2().address(),
                &(user2_balance + (3 * amount)).as_ref(),
            )?;

            Ok(())
        })
    }
}
