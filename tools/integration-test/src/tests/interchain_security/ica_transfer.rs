//! The following tests are for the Interchain Security.
//! These tests require the first chain to be a Provider chain and
//! the second chain a Consumer chain.
use std::str::FromStr;

use ibc_relayer_types::applications::ics27_ica::cosmos_tx::CosmosTx;
use ibc_relayer_types::applications::ics27_ica::packet_data::InterchainAccountPacketData;
use ibc_relayer_types::applications::transfer::msgs::send::MsgSend;
use ibc_relayer_types::applications::transfer::{Amount, Coin};
use ibc_relayer_types::bigint::U256;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_test_framework::chain::config::add_allow_message_interchainaccounts;
use ibc_test_framework::chain::ext::ica::register_unordered_interchain_account;
use ibc_test_framework::framework::binary::channel::run_binary_interchain_security_channel_test;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::assert_eventually_channel_established;
use ibc_test_framework::util::interchain_security::{
    interchain_send_tx, update_genesis_for_consumer_chain, update_relayer_config_for_consumer_chain,
};

#[test]
fn test_ics_ica_transfer() -> Result<(), Error> {
    run_binary_interchain_security_channel_test(&InterchainSecurityIcaTransferTest)
}

struct InterchainSecurityIcaTransferTest;

impl TestOverrides for InterchainSecurityIcaTransferTest {
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        add_allow_message_interchainaccounts(genesis, "/cosmos.bank.v1beta1.MsgSend")?;
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
        config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let fee_denom_a: MonoTagged<ChainA, Denom> =
            MonoTagged::new(Denom::base(config.native_token(0)));
        let connection_b_to_a = channel.connection.clone().flip();
        let (wallet, channel_id, port_id) = register_unordered_interchain_account(
            &chains.node_b,
            chains.handle_b(),
            &connection_b_to_a,
        )?;

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
            &fee_denom_a.with_amount(381000000u64).as_ref(),
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
