//! The following tests are for the Interchain Security.
//! These tests require the first chain to be a Provider chain and
//! the second chain a Consumer chain.
use std::str::FromStr;

use ibc_relayer::{
    chain::tracking::TrackedMsgs,
    event::IbcEventWithHeight,
};
use ibc_relayer_types::{
    applications::{
        ics27_ica::{
            cosmos_tx::CosmosTx,
            msgs::send_tx::MsgSendTx,
            packet_data::InterchainAccountPacketData,
        },
        transfer::{
            msgs::send::MsgSend,
            Amount,
            Coin,
        },
    },
    bigint::U256,
    signer::Signer,
    timestamp::Timestamp,
    tx_msg::Msg,
};
use ibc_test_framework::{
    chain::ext::ica::register_interchain_account,
    framework::binary::channel::run_binary_interchain_security_channel_test,
    prelude::*,
    relayer::channel::assert_eventually_channel_established,
    util::interchain_security::{
        update_genesis_for_consumer_chain,
        update_relayer_config_for_consumer_chain,
    },
};

#[test]
fn test_ics_ica_transfer() -> Result<(), Error> {
    run_binary_interchain_security_channel_test(&InterchainSecurityIcaTransferTest)
}

struct InterchainSecurityIcaTransferTest;

impl TestOverrides for InterchainSecurityIcaTransferTest {
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

    // The `ccv_consumer_chain` must be `true` for the Consumer chain.
    // The `trusting_period` must be strictly smaller than the `unbonding_period`
    // specified in the Consumer chain proposal. The test framework uses 100s in
    // the proposal.
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        update_relayer_config_for_consumer_chain(config);
    }
}

impl BinaryChannelTest for InterchainSecurityIcaTransferTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
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

        let amount = 12345;

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

        // Send funds from the ICA account to the `user2` account on the host chain on behalf
        // of the `user1` account on the controller chain.
        let ica_events = interchain_send_tx(
            chains.handle_b(),
            &signer,
            &channel.connection.connection_id_b.0,
            interchain_account_packet_data,
            Timestamp::from_nanoseconds(120000000000).unwrap(),
        )?;

        info!("ICA events from `CosmosTx`: {ica_events:#?}");

        // Check that the ICA account's balance has been debited the sent amount.
        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund - amount).as_ref(),
        )?;
        Ok(())
    }
}

fn interchain_send_tx<ChainA: ChainHandle>(
    chain: &ChainA,
    from: &Signer,
    connection: &ConnectionId,
    msg: InterchainAccountPacketData,
    relative_timeout: Timestamp,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    let msg = MsgSendTx {
        owner: from.clone(),
        connection_id: connection.clone(),
        packet_data: msg,
        relative_timeout,
    };

    let msg_any = msg.to_any();

    let tm = TrackedMsgs::new_static(vec![msg_any], "SendTx");

    chain
        .send_messages_and_wait_commit(tm)
        .map_err(Error::relayer)
}
