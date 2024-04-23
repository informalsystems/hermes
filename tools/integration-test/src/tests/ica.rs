use std::collections::HashMap;
use std::str::FromStr;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::config::{
    filter::{ChannelFilters, ChannelPolicy, FilterPattern},
    ChainConfig, PacketFilter,
};
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer_types::applications::ics27_ica::msgs::send_tx::MsgSendTx;
use ibc_relayer_types::applications::ics27_ica::packet_data::InterchainAccountPacketData;
use ibc_relayer_types::applications::{
    ics27_ica::cosmos_tx::CosmosTx,
    transfer::{msgs::send::MsgSend, Amount, Coin},
};
use ibc_relayer_types::bigint::U256;
use ibc_relayer_types::core::ics04_channel::channel::State;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;

use ibc_test_framework::chain::ext::ica::register_interchain_account;
use ibc_test_framework::ibc::denom::Denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::{
    assert_eventually_channel_closed, assert_eventually_channel_established, query_channel_end,
};

#[test]
fn test_ica_filter_default() -> Result<(), Error> {
    run_binary_connection_test(&IcaFilterTestAllow::new(PacketFilter::default()))
}

#[test]
fn test_ica_filter_allow() -> Result<(), Error> {
    run_binary_connection_test(&IcaFilterTestAllow::new(PacketFilter::new(
        ChannelPolicy::Allow(ChannelFilters::new(vec![(
            FilterPattern::Wildcard("ica*".parse().unwrap()),
            FilterPattern::Wildcard("*".parse().unwrap()),
        )])),
        HashMap::new(),
    )))
}

#[test]
fn test_ica_filter_deny() -> Result<(), Error> {
    run_binary_connection_test(&IcaFilterTestDeny)
}

#[test]
fn test_ica_close_channel() -> Result<(), Error> {
    run_binary_connection_test(&ICACloseChannelTest)
}

pub struct IcaFilterTestAllow {
    packet_filter: PacketFilter,
}

impl IcaFilterTestAllow {
    pub fn new(packet_filter: PacketFilter) -> Self {
        Self { packet_filter }
    }
}

impl TestOverrides for IcaFilterTestAllow {
    // Enable channel workers and allow relaying on ICA channels
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        for chain in &mut config.chains {
            match chain {
                ChainConfig::CosmosSdk(chain_config) | ChainConfig::Namada(chain_config) => {
                    chain_config.packet_filter = self.packet_filter.clone();
                }
            }
        }
    }

    // Allow MsgSend messages over ICA
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        use serde_json::Value;

        let allow_messages = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("interchainaccounts"))
            .and_then(|ica| ica.get_mut("host_genesis_state"))
            .and_then(|state| state.get_mut("params"))
            .and_then(|params| params.get_mut("allow_messages"))
            .and_then(|allow_messages| allow_messages.as_array_mut());

        if let Some(allow_messages) = allow_messages {
            allow_messages.push(Value::String("/cosmos.bank.v1beta1.MsgSend".to_string()));
            Ok(())
        } else {
            Err(Error::generic(eyre!("failed to update genesis file")))
        }
    }
}

impl BinaryConnectionTest for IcaFilterTestAllow {
    fn run<Controller: ChainHandle, Host: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<Controller, Host>,
        connection: ConnectedConnection<Controller, Host>,
    ) -> Result<(), Error> {
        // Register an interchain account on behalf of
        // controller wallet `user1` where the counterparty chain is the interchain accounts host.
        let (wallet, channel_id, port_id) =
            register_interchain_account(&chains.node_a, chains.handle_a(), &connection)?;

        // Check that the corresponding ICA channel is eventually established.
        let _counterparty_channel_id = assert_eventually_channel_established(
            chains.handle_a(),
            chains.handle_b(),
            &channel_id.as_ref(),
            &port_id.as_ref(),
        )?;

        // Query the controller chain for the address of the ICA wallet on the host chain.
        let ica_address = chains
            .node_a
            .chain_driver()
            .query_interchain_account(&wallet.address(), &connection.connection_id_a.as_ref())?;

        let stake_denom: MonoTagged<Host, Denom> = MonoTagged::new(Denom::base("stake", "stake"));

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(0u64).as_ref(),
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
        // of the `user1` account on the controller chain.
        interchain_send_tx(
            chains.handle_a(),
            &signer,
            &connection.connection_id_a.0,
            interchain_account_packet_data,
            Timestamp::from_nanoseconds(120000000000).unwrap(),
        )?;

        // Check that the ICA account's balance has been debited the sent amount.
        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund - amount).as_ref(),
        )?;
        Ok(())
    }
}
pub struct IcaFilterTestDeny;

impl TestOverrides for IcaFilterTestDeny {
    // Enable channel workers and deny ICA ports
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        for chain in &mut config.chains {
            match chain {
                ChainConfig::CosmosSdk(chain_config) | ChainConfig::Namada(chain_config) => {
                    chain_config.packet_filter.channel_policy =
                        ChannelPolicy::Deny(ChannelFilters::new(vec![(
                            FilterPattern::Wildcard("ica*".parse().unwrap()),
                            FilterPattern::Wildcard("*".parse().unwrap()),
                        )]));
                }
            }
        }
    }
}

impl BinaryConnectionTest for IcaFilterTestDeny {
    fn run<Controller: ChainHandle, Host: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<Controller, Host>,
        connection: ConnectedConnection<Controller, Host>,
    ) -> Result<(), Error> {
        // Register an interchain account on behalf of controller wallet `user1`
        // where the counterparty chain is the interchain accounts host.
        let (_, channel_id, port_id) =
            register_interchain_account(&chains.node_a, chains.handle_a(), &connection)?;

        // Wait a bit, the relayer will refuse to complete the channel handshake
        // because the port is explicitly disallowed by the filter.
        std::thread::sleep(Duration::from_secs(30));

        let channel_end =
            query_channel_end(chains.handle_a(), &channel_id.as_ref(), &port_id.as_ref())?;

        // Check that the channel is left in state Init
        assert_eq(
            "channel end should still be in state Init",
            channel_end.value().state(),
            &State::Init,
        )
    }
}

pub struct ICACloseChannelTest;

impl TestOverrides for ICACloseChannelTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        config.mode.clients.misbehaviour = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryConnectionTest for ICACloseChannelTest {
    fn run<Controller: ChainHandle, Host: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Controller, Host>,
        connection: ConnectedConnection<Controller, Host>,
    ) -> Result<(), Error> {
        let gas_denom_str = match relayer
            .config
            .chains
            .first()
            .ok_or_else(|| eyre!("chain configuration is empty"))?
        {
            ChainConfig::CosmosSdk(chain_config) | ChainConfig::Namada(chain_config) => {
                chain_config.gas_price.denom.clone()
            }
        };
        let stake_denom: MonoTagged<Host, Denom> =
            MonoTagged::new(Denom::base(&gas_denom_str, &gas_denom_str));
        let (wallet, ica_address, controller_channel_id, controller_port_id) = relayer
            .with_supervisor(|| {
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

                // Query the controller chain for the address of the ICA wallet on the host chain.
                let ica_address = chains.node_a.chain_driver().query_interchain_account(
                    &wallet.address(),
                    &connection.connection_id_a.as_ref(),
                )?;

                chains.node_b.chain_driver().assert_eventual_wallet_amount(
                    &ica_address.as_ref(),
                    &stake_denom.with_amount(0u64).as_ref(),
                )?;

                Ok((
                    wallet,
                    ica_address,
                    controller_channel_id,
                    controller_port_id,
                ))
            })?;

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

        let amount = 12345u64;

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

        let balance_user2 = chains.node_b.chain_driver().query_balance(
            &chains.node_b.wallets().user2().address(),
            &stake_denom.as_ref(),
        )?;

        interchain_send_tx(
            chains.handle_a(),
            &signer,
            &connection.connection_id_a.0,
            interchain_account_packet_data,
            Timestamp::from_nanoseconds(1000000000).unwrap(),
        )?;

        sleep(Duration::from_nanos(3000000000));

        relayer.with_supervisor(|| {
            // Check that user2 has not received the sent amount.
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &chains.node_b.wallets().user2().address(),
                &(balance_user2).as_ref(),
            )?;
            sleep(Duration::from_secs(5));

            // Check that the ICA account's balance has not been debited the sent amount.
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &ica_address.as_ref(),
                &stake_denom.with_amount(ica_fund).as_ref(),
            )?;

            info!("Check that the channel closed after packet timeout...");

            assert_eventually_channel_closed(
                &chains.handle_a,
                &chains.handle_b,
                &controller_channel_id.as_ref(),
                &controller_port_id.as_ref(),
            )?;

            Ok(())
        })
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
