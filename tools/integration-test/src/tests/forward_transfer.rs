use ibc_test_framework::prelude::*;

#[test]
fn test_ibc_forward_transfer() -> Result<(), Error> {
    run_nary_channel_test(&IbcForwardTransferTest)
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

        // Build the recipient address as following:
        // {intermediate_refund_address}|{foward_port}/{forward_channel}:{final_destination_address}
        // See https://hub.cosmos.network/main/governance/proposals/2021-09-hub-ibc-router/
        let forward_a_to_c_from_b = format!(
            "{}|{}/{}:{}",
            &wallet_b.address(),
            channel_b_to_c.port_a,
            channel_b_to_c.channel.src_channel_id().unwrap(),
            &wallet_c.address()
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
            &MonoTagged::new(&WalletAddress(forward_a_to_c_from_b)),
            &denom_a.with_amount(a_to_c_amount).as_ref(),
        )?;

        let denom_b = derive_ibc_denom(
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let denom_a_to_c = derive_ibc_denom(
            &channel_b_to_c.port_b.as_ref(),
            &channel_b_to_c.channel_id_b.as_ref(),
            &denom_b.as_ref(),
        )?;

        info!(
            "Waiting for user on chain C to receive IBC transferred amount of {}",
            a_to_c_amount
        );

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_c_amount).as_ref(),
        )?;

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
