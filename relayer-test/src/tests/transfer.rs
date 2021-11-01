use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use crate::bootstrap::deployment::ChainDeployment;
use crate::error::Error;
use crate::ibc::denom::derive_ibc_denom;
use crate::relayer::channel::Channel;
use crate::traits::base::TestWithDefault;
use crate::traits::binary::channel::{run_two_way_binary_channel_test, BinaryChannelTestCase};
use crate::util::random::random_u64_range;

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    run_two_way_binary_channel_test(IbcTransferTest)
}

struct IbcTransferTest;

impl TestWithDefault for IbcTransferTest {}

impl BinaryChannelTestCase for IbcTransferTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: &ChainDeployment<ChainA, ChainB>,
        channel: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.side_a.denom();

        let chaina_user1_balance = chains
            .side_a
            .chain_driver()
            .query_balance(&chains.side_a.wallets().user1().address(), &denom_a)?;

        let a_to_b_amount = random_u64_range(1000, 5000);

        info!("Sending IBC transfer");

        chains.side_a.chain_driver().transfer_token(
            &channel.port_a,
            &channel.channel_id_a,
            &chains.side_a.wallets().user1().address(),
            &chains.side_b.wallets().user1().address(),
            a_to_b_amount,
            &denom_a,
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!(
            "Waiting for user on chain B to receive transfer in denom {}",
            denom_b.value().0
        );

        chains.side_a.chain_driver().assert_eventual_wallet_amount(
            &chains.side_a.wallets().user1(),
            chaina_user1_balance - a_to_b_amount,
            &denom_a,
        )?;

        chains.side_b.chain_driver().assert_eventual_wallet_amount(
            &chains.side_b.wallets().user1(),
            a_to_b_amount,
            &denom_b.as_ref(),
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            chains.side_a.chain_id(),
            chains.side_b.chain_id(),
        );

        let chaina_user2_balance = chains
            .side_a
            .chain_driver()
            .query_balance(&chains.side_a.wallets().user2().address(), &denom_a)?;

        let b_to_a_amount = random_u64_range(500, a_to_b_amount);

        chains.side_b.chain_driver().transfer_token(
            &channel.port_b,
            &channel.channel_id_b,
            &chains.side_b.wallets().user1().address(),
            &chains.side_a.wallets().user2().address(),
            b_to_a_amount,
            &denom_b.as_ref(),
        )?;

        chains.side_b.chain_driver().assert_eventual_wallet_amount(
            &chains.side_b.wallets().user1(),
            a_to_b_amount - b_to_a_amount,
            &denom_b.as_ref(),
        )?;

        chains.side_a.chain_driver().assert_eventual_wallet_amount(
            &chains.side_a.wallets().user2(),
            chaina_user2_balance + b_to_a_amount,
            &denom_a,
        )?;

        info!(
            "successfully performed reverse IBC transfer from chain {} back to chain {}",
            chains.side_b.chain_id(),
            chains.side_a.chain_id(),
        );

        Ok(())
    }
}
