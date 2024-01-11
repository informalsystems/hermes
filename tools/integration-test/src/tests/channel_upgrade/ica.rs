//! Tests channel upgrade features:
//!
//! - `ChannelUpgradeICACloseChannel` tests that after the upgrade handshake is completed
//!   and the channel version has been updated to ICS29 a packet timeout closes the channel.

use std::str::FromStr;
use serde_json as json;

use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};

use ibc_relayer::event::IbcEventWithHeight;

use ibc_relayer_types::bigint::U256;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::applications::{
    ics27_ica,
    ics27_ica::{cosmos_tx::CosmosTx, msgs::send_tx::MsgSendTx, packet_data::InterchainAccountPacketData},
    transfer::{msgs::send::MsgSend, Amount, Coin},
};

use ibc_test_framework::chain::ext::ica::register_interchain_account;
use ibc_test_framework::chain::config::{set_max_deposit_period, set_voting_period};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::{
    assert_eventually_channel_established, 
    assert_eventually_channel_closed,
    assert_eventually_channel_upgrade_open,
    ChannelUpgradableAttributes,
};

#[test]
fn test_channel_upgrade_ica_close_channel() -> Result<(), Error> {
    run_binary_connection_test(&ChannelUpgradeICACloseChannel)
}

const MAX_DEPOSIT_PERIOD: &str = "10s";
const VOTING_PERIOD: u64 = 10;

pub struct ChannelUpgradeICACloseChannel;

impl TestOverrides for ChannelUpgradeICACloseChannel {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;
        config.mode.packets.auto_register_counterparty_payee = true;
        config.mode.packets.clear_interval = 0;
        config.mode.packets.clear_on_start = false;

        config.mode.clients.misbehaviour = false;
    }

    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        set_max_deposit_period(genesis, MAX_DEPOSIT_PERIOD)?;
        set_voting_period(genesis, VOTING_PERIOD)?;
        Ok(())
    }
}

impl BinaryConnectionTest for ChannelUpgradeICACloseChannel {
    fn run<Controller: ChainHandle, Host: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<Controller, Host>,
        connection: ConnectedConnection<Controller, Host>,
    ) -> Result<(), Error> {
        // Register an interchain account on behalf of
        // controller wallet `user1` where the counterparty chain is the interchain accounts host.
        let (wallet, controller_channel_id, controller_port_id) =
            register_interchain_account(&chains.node_a, chains.handle_a(), &connection)?;

        // Check that the corresponding ICA channel is eventually established.
        let _counterparty_channel_id = assert_eventually_channel_established(
            chains.handle_a(),
            chains.handle_b(),
            &controller_channel_id.as_ref(),
            &controller_port_id.as_ref(),
        )?;
        
        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: controller_port_id.value().clone(),
                    channel_id: controller_channel_id.value().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let host_port_id = channel_end_a.remote.port_id;
        let host_channel_id = channel_end_a.remote.channel_id.ok_or_else(|| eyre!("expect to find counterparty channel id"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: host_port_id.clone(),
                    channel_id: host_channel_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        // Query the controller chain for the address of the ICA wallet on the host chain.
        let ica_address = chains
            .node_a
            .chain_driver()
            .query_interchain_account(&wallet.address(), &connection.connection_id_a.as_ref())?;

        let stake_denom: MonoTagged<Host, Denom> = MonoTagged::new(Denom::base("stake"));

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(0u64).as_ref(),
        )?;

        let app_version = json::json!({
            "version": ics27_ica::VERSION,
            "encoding": "proto3",
            "tx_type": "sdk_multi_msg",
            "address": ica_address.to_string(),
            "controller_connection_id": connection.connection_id_a.0,
            "host_connection_id": connection.connection_id_b.0,
        });
        let new_version = Version::ics27_with_fee(&app_version.to_string());

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            controller_port_id.to_string().as_str(),
            controller_channel_id.to_string().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the channel upgrade successfully upgraded the version...");

        assert_eventually_channel_upgrade_open(
            &chains.handle_a,
            &chains.handle_b,
            &controller_channel_id.as_ref(),
            &controller_port_id.as_ref(),
            &upgraded_attrs,
        )?;
        
        // Send funds to the interchain account.
        let ica_fund = 42000u64;

        chains.node_b.chain_driver().local_transfer_token(
            &chains.node_b.wallets().user1(),
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund).as_ref(),
        )?;

        let amount = 12345;

        let msg = MsgSend {
            from_address: ica_address.to_string(),
            to_address: chains.node_b.wallets().user2().address().to_string(),
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
        // of the `user1` account on the controller chain. The timeout is set to 1s to force a 
        // packet timeout that will close the channel.
        interchain_send_tx(
            chains.handle_a(),
            &signer,
            &connection.connection_id_a.0,
            interchain_account_packet_data,
            Timestamp::from_nanoseconds(1000000000).unwrap(),
        )?;

        sleep(Duration::from_secs(5));

        // Check that the ICA account's balance has not been debited the sent amount.
        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund).as_ref(),
        )?;

        //
        info!("Check that the channel closed after packet timeout...");

        assert_eventually_channel_closed(
            &chains.handle_a,
            &chains.handle_b,
            &controller_channel_id.as_ref(),
            &controller_port_id.as_ref(),
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
