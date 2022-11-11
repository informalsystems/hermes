//! This test tests three different cases:
//!
//! - The `IbcForwardTransferTest` tests the case a packet is successfully
//!   forwarded.
//!
//! - The `InvalidChannelIbcForwardTransferTest` tests the case where the
//!   sender is refunded if the forward channel specified is invalid.
//!
//! - The `InvalidAddressIbcForwardTransferTest` tests the case when the destination
//!   address is invalid. This results in two scenarios depending on the Gaia
//!   version.
//!   For Gaia 6 the intermediate address will receive the refunded tokens.
//!   For Gaia 8 the sender will receive the refunded tokens.

use ibc_test_framework::chain::ext::forward::{
    build_forward_address, build_invalid_forward_address,
};
use ibc_test_framework::chain::ext::version::ChainVersionMethodsExt;
use ibc_test_framework::prelude::*;

#[test]
fn test_ibc_forward_transfer() -> Result<(), Error> {
    run_nary_channel_test(&IbcForwardTransferTest)
}

#[test]
fn test_invalid_channel_ibc_forward_transfer() -> Result<(), Error> {
    run_nary_channel_test(&InvalidChannelIbcForwardTransferTest)
}

#[test]
fn test_invalid_address_ibc_forward_transfer() -> Result<(), Error> {
    run_nary_channel_test(&InvalidAddressIbcForwardTransferTest)
}
pub struct IbcForwardTransferTest;

impl TestOverrides for IbcForwardTransferTest {}

impl PortsOverride<3> for IbcForwardTransferTest {}

impl NaryChannelTest<3> for IbcForwardTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 3>,
        channels: NaryConnectedChannels<Handle, 3>,
    ) -> Result<(), Error> {
        let connected_chains = chains.connected_chains_at::<0, 2>()?;
        let node_a = chains.full_node_at::<0>()?;
        let node_b = chains.full_node_at::<1>()?;
        let node_c = chains.full_node_at::<2>()?;

        let channel_a_to_b = channels.channel_at::<0, 1>()?;
        let channel_b_to_c = channels.channel_at::<1, 2>()?;

        let denom_a = connected_chains.node_a.denom();

        let binding = node_a.wallets();
        let wallet_a = binding.user1();
        let binding = node_b.wallets();
        let wallet_b = binding.user1();
        let binding = node_c.wallets();
        let wallet_c = binding.user1();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_c_amount = 4000_u128;

        let denom_b = derive_ibc_denom(
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let balance_b = node_b
            .chain_driver()
            .query_balance(&wallet_b.address(), &denom_b.as_ref())?;

        let denom_a_to_c = derive_ibc_denom(
            &channel_b_to_c.port_b.as_ref(),
            &channel_b_to_c.channel_id_b.as_ref(),
            &denom_b.as_ref(),
        )?;

        let forward_a_to_c_from_b = build_forward_address(
            wallet_b.address(),
            channel_b_to_c.port_a,
            channel_b_to_c.channel.src_channel_id().unwrap(),
            wallet_c.address(),
        );

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}, through address {}",
            chains.chain_handle_at::<0>().unwrap().value(),
            chains.chain_handle_at::<2>().unwrap().value(),
            a_to_c_amount,
            denom_a,
            forward_a_to_c_from_b
        );

        node_a.chain_driver().ibc_transfer_token(
            &channel_a_to_b.port_a.as_ref(),
            &channel_a_to_b.channel_id_a.as_ref(),
            &wallet_a,
            &MonoTagged::new(&forward_a_to_c_from_b),
            &denom_a.with_amount(a_to_c_amount).as_ref(),
        )?;

        info!(
            "Waiting for user on chain C to receive IBC transferred amount of {}",
            a_to_c_amount
        );

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_c_amount).as_ref(),
        )?;

        node_b
            .chain_driver()
            .assert_eventual_wallet_amount(&wallet_b.address(), &(balance_b).as_ref())?;

        node_c.chain_driver().assert_eventual_wallet_amount(
            &wallet_c.address(),
            &denom_a_to_c.with_amount(a_to_c_amount).as_ref(),
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            chains.chain_handle_at::<0>().unwrap().value(),
            chains.chain_handle_at::<2>().unwrap().value(),
        );

        Ok(())
    }
}

pub struct InvalidChannelIbcForwardTransferTest;

impl TestOverrides for InvalidChannelIbcForwardTransferTest {
    // Ensure the invalid channel doesn't exist
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }
}

impl PortsOverride<3> for InvalidChannelIbcForwardTransferTest {}

impl NaryChannelTest<3> for InvalidChannelIbcForwardTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 3>,
        channels: NaryConnectedChannels<Handle, 3>,
    ) -> Result<(), Error> {
        let connected_chains = chains.connected_chains_at::<0, 2>()?;
        let node_a = chains.full_node_at::<0>()?;
        let node_b = chains.full_node_at::<1>()?;
        let node_c = chains.full_node_at::<2>()?;

        let channel_a_to_b = channels.channel_at::<0, 1>()?;
        let channel_b_to_c = channels.channel_at::<1, 2>()?;

        let denom_a = connected_chains.node_a.denom();

        let binding = node_a.wallets();
        let wallet_a = binding.user1();
        let binding = node_b.wallets();
        let wallet_b = binding.user1();
        let binding = node_c.wallets();
        let wallet_c = binding.user1();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_c_amount = 4000_u128;

        let denom_b = derive_ibc_denom(
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let balance_b = node_b
            .chain_driver()
            .query_balance(&wallet_b.address(), &denom_b.as_ref())?;

        let denom_a_to_c = derive_ibc_denom(
            &channel_b_to_c.port_b.as_ref(),
            &channel_b_to_c.channel_id_b.as_ref(),
            &denom_b.as_ref(),
        )?;

        let balance_c = node_c
            .chain_driver()
            .query_balance(&wallet_c.address(), &denom_a_to_c.as_ref())?;

        let invalid_channel = ChannelId::new(9999);

        let forward_a_to_c_from_b = build_forward_address(
            wallet_b.address(),
            channel_b_to_c.port_a,
            &invalid_channel,
            wallet_c.address(),
        );

        info!(
            "Trying to send IBC transfer from chain {} to chain {} with amount of {} {}, through address {}",
            chains.chain_handle_at::<0>().unwrap().value(),
            chains.chain_handle_at::<2>().unwrap().value(),
            a_to_c_amount,
            denom_a,
            forward_a_to_c_from_b
        );

        node_a.chain_driver().ibc_transfer_token(
            &channel_a_to_b.port_a.as_ref(),
            &channel_a_to_b.channel_id_a.as_ref(),
            &wallet_a,
            &MonoTagged::new(&forward_a_to_c_from_b),
            &denom_a.with_amount(a_to_c_amount).as_ref(),
        )?;

        sleep(Duration::from_secs(2));

        // The sender will still lose the tokens if the channel is invalid.
        node_a
            .chain_driver()
            .assert_eventual_wallet_amount(&wallet_a.address(), &(balance_a).as_ref())?;

        node_b
            .chain_driver()
            .assert_eventual_wallet_amount(&wallet_b.address(), &(balance_b).as_ref())?;

        // The expected receiver will never receive the token.
        node_c
            .chain_driver()
            .assert_eventual_wallet_amount(&wallet_c.address(), &(balance_c).as_ref())?;

        Ok(())
    }
}

pub struct InvalidAddressIbcForwardTransferTest;

impl TestOverrides for InvalidAddressIbcForwardTransferTest {
    // Ensure the invalid channel doesn't exist
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }
}

impl PortsOverride<3> for InvalidAddressIbcForwardTransferTest {}

impl NaryChannelTest<3> for InvalidAddressIbcForwardTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 3>,
        channels: NaryConnectedChannels<Handle, 3>,
    ) -> Result<(), Error> {
        let connected_chains = chains.connected_chains_at::<0, 2>()?;
        let node_a = chains.full_node_at::<0>()?;
        let node_b = chains.full_node_at::<1>()?;
        let node_c = chains.full_node_at::<2>()?;

        let channel_a_to_b = channels.channel_at::<0, 1>()?;
        let channel_b_to_c = channels.channel_at::<1, 2>()?;

        let denom_a = connected_chains.node_a.denom();

        let binding = node_a.wallets();
        let wallet_a = binding.user1();
        let binding = node_b.wallets();
        let wallet_b = binding.user1();
        let binding = node_c.wallets();
        let wallet_c = binding.user1();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_c_amount = 4000_u128;

        let denom_b = derive_ibc_denom(
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let balance_b = node_b
            .chain_driver()
            .query_balance(&wallet_b.address(), &denom_b.as_ref())?;

        let denom_a_to_c = derive_ibc_denom(
            &channel_b_to_c.port_b.as_ref(),
            &channel_b_to_c.channel_id_b.as_ref(),
            &denom_b.as_ref(),
        )?;

        let balance_c = node_c
            .chain_driver()
            .query_balance(&wallet_c.address(), &denom_a_to_c.as_ref())?;

        let forward_a_to_c_from_b = build_invalid_forward_address(
            wallet_b.address(),
            channel_b_to_c.port_a,
            channel_b_to_c.channel.src_channel_id().unwrap(),
        );

        info!(
            "Trying to send IBC transfer from chain {} to chain {} with amount of {} {}, through address {}",
            chains.chain_handle_at::<0>().unwrap().value(),
            chains.chain_handle_at::<2>().unwrap().value(),
            a_to_c_amount,
            denom_a,
            forward_a_to_c_from_b
        );

        node_a.chain_driver().ibc_transfer_token(
            &channel_a_to_b.port_a.as_ref(),
            &channel_a_to_b.channel_id_a.as_ref(),
            &wallet_a,
            &MonoTagged::new(&forward_a_to_c_from_b),
            &denom_a.with_amount(a_to_c_amount).as_ref(),
        )?;

        sleep(Duration::from_secs(2));

        match node_a.chain_driver().major_version() {
            Ok(6) => {
                // The sender will still lose the tokens since the intermediary chain
                // will get the refunded token.
                node_a.chain_driver().assert_eventual_wallet_amount(
                    &wallet_a.address(),
                    &(balance_a - a_to_c_amount).as_ref(),
                )?;

                // The intemediary chain gets the refunded tokens
                node_b.chain_driver().assert_eventual_wallet_amount(
                    &wallet_b.address(),
                    &(balance_b + a_to_c_amount).as_ref(),
                )?;

                // The expected receiver will never receive the token.
                node_c
                    .chain_driver()
                    .assert_eventual_wallet_amount(&wallet_c.address(), &(balance_c).as_ref())?;

                Ok(())
            }
            Ok(8) => {
                // The sender will get refunded.
                node_a
                    .chain_driver()
                    .assert_eventual_wallet_amount(&wallet_a.address(), &(balance_a).as_ref())?;

                // The intermediary chain doesn't get any tokens.
                node_b
                    .chain_driver()
                    .assert_eventual_wallet_amount(&wallet_b.address(), &(balance_b).as_ref())?;

                // The expected receiver will never receive the token.
                node_c
                    .chain_driver()
                    .assert_eventual_wallet_amount(&wallet_c.address(), &(balance_c).as_ref())?;

                Ok(())
            }
            Ok(v) => Err(Error::generic(eyre!("Major version is not handled: {}", v))),
            Err(e) => Err(Error::generic(eyre!(
                "Failed to retrieve major version: {}",
                e
            ))),
        }
    }
}
