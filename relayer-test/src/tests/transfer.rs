use core::str::FromStr;
use eyre::Report as Error;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use crate::bootstrap::deployment::ChainDeployment;
use crate::bootstrap::pair::boostrap_chain_pair;
use crate::bootstrap::single::wait_wallet_amount;
use crate::chain::builder::ChainBuilder;
use crate::ibc::denom::derive_ibc_denom;
use crate::init::init_test;
use crate::relayer::channel::{bootstrap_channel, Channel};
use crate::tagged::*;
use crate::util::random_u64_range;

#[test]
fn test_chain_manager() -> Result<(), Error> {
    fn test_ibc_transfer<ChainA: ChainHandle, ChainB: ChainHandle>(
        deployment: &ChainDeployment<ChainA, ChainB>,
        channel: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = deployment.side_a.denom();

        let chaina_user1_balance = deployment
            .side_a
            .chain_driver()
            .query_balance(&deployment.side_a.wallets().user1().address(), &denom_a)?;

        let a_to_b_amount = random_u64_range(1000, 5000);

        info!("Sending IBC transfer");

        deployment.side_a.chain_driver().transfer_token(
            &channel.port_a,
            &channel.channel_id_a,
            &deployment.side_a.wallets().user1().address(),
            &deployment.side_b.wallets().user1().address(),
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

        wait_wallet_amount(
            &deployment.side_a.chain_driver(),
            &deployment.side_a.wallets().user1(),
            chaina_user1_balance - a_to_b_amount,
            &denom_a,
            20,
        )?;

        wait_wallet_amount(
            &deployment.side_b.chain_driver(),
            &deployment.side_b.wallets().user1(),
            a_to_b_amount,
            &denom_b.as_ref(),
            20,
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            deployment.side_a.chain_id(),
            deployment.side_b.chain_id(),
        );

        let chaina_user2_balance = deployment
            .side_a
            .chain_driver()
            .query_balance(&deployment.side_a.wallets().user2().address(), &denom_a)?;

        let b_to_a_amount = random_u64_range(500, a_to_b_amount);

        deployment.side_b.chain_driver().transfer_token(
            &channel.port_b,
            &channel.channel_id_b,
            &deployment.side_b.wallets().user1().address(),
            &deployment.side_a.wallets().user2().address(),
            b_to_a_amount,
            &denom_b.as_ref(),
        )?;

        wait_wallet_amount(
            &deployment.side_b.chain_driver(),
            &deployment.side_b.wallets().user1(),
            a_to_b_amount - b_to_a_amount,
            &denom_b.as_ref(),
            20,
        )?;

        wait_wallet_amount(
            &deployment.side_a.chain_driver(),
            &deployment.side_a.wallets().user2(),
            chaina_user2_balance + b_to_a_amount,
            &denom_a,
            20,
        )?;

        info!(
            "successfully performed reverse IBC transfer from chain {} back to chain {}",
            deployment.side_b.chain_id(),
            deployment.side_a.chain_id(),
        );

        Ok(())
    }

    init_test()?;

    let builder = ChainBuilder::new("gaiad", "data");

    let deployment = boostrap_chain_pair(&builder)?;

    let port = PortId::from_str("transfer")?;
    let port_a = DualTagged::new(port.clone());
    let port_b = DualTagged::new(port);

    let channel = bootstrap_channel(
        &deployment.client_b_to_a,
        &deployment.client_a_to_b,
        &port_a,
        &port_b,
    )?;

    info!("created new channel {:?}", channel);

    test_ibc_transfer(&deployment, &channel)?;
    test_ibc_transfer(&deployment.flip(), &channel.flip())?;

    // std::thread::sleep(Duration::from_secs(1));

    Ok(())
}
