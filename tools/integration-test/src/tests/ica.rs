use std::str::FromStr;

use serde::Serialize;

use ibc_relayer::config::{
    filter::{ChannelFilters, FilterPattern},
    PacketFilter,
};
use ibc_relayer_types::core::ics04_channel::channel::State;

use ibc_test_framework::{
    ibc::denom::Denom,
    prelude::*,
    relayer::channel::{assert_eventually_channel_established, query_channel_end},
};

#[test]
fn test_ica_filter_default() -> Result<(), Error> {
    run_binary_connection_test(&IcaFilterTestAllow::new(PacketFilter::default()))
}

#[test]
fn test_ica_filter_allow() -> Result<(), Error> {
    run_binary_connection_test(&IcaFilterTestAllow::new(PacketFilter::Allow(
        ChannelFilters::new(vec![(
            FilterPattern::Wildcard("ica*".parse().unwrap()),
            FilterPattern::Wildcard("*".parse().unwrap()),
        )]),
    )))
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
            chain.packet_filter = self.packet_filter.clone();
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
        relayer: RelayerDriver,
        chains: ConnectedChains<Controller, Host>,
        connection: ConnectedConnection<Controller, Host>,
    ) -> Result<(), Error> {
        // Register an interchain account on behalf of
        // controller wallet `user1` where the counterparty chain is the interchain accounts host.
        // Then spawn the supervisor.
        let (_handle, wallet, channel_id, port_id) =
            register_interchain_account(&relayer, &chains, &connection)?;

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

        let stake_denom: MonoTagged<Host, Denom> = MonoTagged::new(Denom::base("stake"));

        // Query the interchain account balance on the host chain. It should be empty.
        let ica_balance = chains
            .node_b
            .chain_driver()
            .query_balance(&ica_address.as_ref(), &stake_denom.as_ref())?;

        assert_eq(
            "balance of ICA account should be 0",
            &ica_balance.amount(),
            &0u64.into(),
        )?;

        // Send funds to the interchain account.
        let ica_fund = 42000u64;

        chains.node_b.chain_driver().local_transfer_token(
            &chains.node_b.wallets().user1(),
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund).as_ref(),
        )?;

        #[derive(Serialize)]
        struct MsgSend {
            #[serde(rename = "@type")]
            tpe: String,
            from_address: String,
            to_address: String,
            amount: Vec<Amount>,
        }

        #[derive(Serialize)]
        struct Amount {
            denom: String,
            amount: String,
        }

        let amount = 12345;

        let msg = MsgSend {
            tpe: "/cosmos.bank.v1beta1.MsgSend".to_string(),
            from_address: ica_address.to_string(),
            to_address: chains.node_a.wallets().user2().address().to_string(),
            amount: vec![Amount {
                denom: stake_denom.to_string(),
                amount: amount.to_string(),
            }],
        };

        // Send funds from the ICA account to the `user2` account on the host chain on behalf
        // of the `user1` account on the controller chain.
        chains.node_a.chain_driver().interchain_submit(
            &wallet.address(),
            &connection.connection_id_a.as_ref(),
            &msg,
        )?;

        // Check that the ICA account's balance has been debited the sent amount.
        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &ica_address.as_ref(),
            &stake_denom.with_amount(ica_fund - amount).as_ref(),
        )?;

        Ok(())
    }
}

#[test]
fn test_ica_filter_deny() -> Result<(), Error> {
    run_binary_connection_test(&IcaFilterTestDeny)
}

pub struct IcaFilterTestDeny;

impl TestOverrides for IcaFilterTestDeny {
    // Enable channel workers and deny ICA ports
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        for chain in &mut config.chains {
            chain.packet_filter = PacketFilter::Deny(ChannelFilters::new(vec![(
                FilterPattern::Wildcard("ica*".parse().unwrap()),
                FilterPattern::Wildcard("*".parse().unwrap()),
            )]));
        }
    }
}

impl BinaryConnectionTest for IcaFilterTestDeny {
    fn run<Controller: ChainHandle, Host: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Controller, Host>,
        connection: ConnectedConnection<Controller, Host>,
    ) -> Result<(), Error> {
        // Register an interchain account on behalf of controller wallet `user1`
        // where the counterparty chain is the interchain accounts host.
        // Then spawn the supervisor.
        let (_handle, _, channel_id, port_id) =
            register_interchain_account(&relayer, &chains, &connection)?;

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

#[allow(clippy::type_complexity)]
fn register_interchain_account<ChainA: ChainHandle, ChainB: ChainHandle>(
    relayer: &RelayerDriver,
    chains: &ConnectedChains<ChainA, ChainB>,
    connection: &ConnectedConnection<ChainA, ChainB>,
) -> Result<
    (
        SupervisorHandle,
        MonoTagged<ChainA, Wallet>,
        TaggedChannelId<ChainA, ChainB>,
        TaggedPortId<ChainA, ChainB>,
    ),
    Error,
> {
    let wallet = chains.node_a.wallets().user1().cloned();
    let handle = relayer.spawn_supervisor()?;

    chains
        .node_a
        .chain_driver()
        .register_interchain_account(&wallet.address(), &connection.connection_id_a.as_ref())?;

    let channel_id: TaggedChannelId<ChainA, ChainB> =
        TaggedChannelId::new("channel-0".parse().unwrap());

    let icacontroller =
        PortId::from_str(&format!("icacontroller-{}", wallet.address().value())).unwrap();

    let port_id: TaggedPortId<ChainA, ChainB> = TaggedPortId::new(icacontroller);

    Ok((handle, wallet, channel_id, port_id))
}
