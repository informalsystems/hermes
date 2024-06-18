use crate::chain::cli::authz::{authz_grant, exec_grant, query_authz_grant};
use crate::chain::cli::transfer::generate_transfer_from_chain_tx;
use crate::error::Error;
use crate::prelude::*;
use crate::types::tagged::MonoTagged;

use super::bootstrap::ChainBootstrapMethodsExt;

const WAIT_GRANT_ATTEMPTS: u16 = 5;

pub trait AuthzMethodsExt<Chain> {
    fn authz_grant(
        &self,
        granter: &str,
        grantee: &str,
        msg_type: &str,
        fees: &str,
    ) -> Result<(), Error>;

    fn assert_eventual_grant(
        &self,
        granter: &str,
        grantee: &str,
        msg_type: &str,
    ) -> Result<(), Error>;

    fn exec_ibc_transfer_grant<Counterparty>(
        &self,
        granter: &str,
        grantee: &str,
        port: &PortId,
        channel: &ChannelId,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        fees: &str,
    ) -> Result<(), Error>;
}

impl<'a, Chain: Send> AuthzMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn authz_grant(
        &self,
        granter: &str,
        grantee: &str,
        msg_type: &str,
        fees: &str,
    ) -> Result<(), Error> {
        authz_grant(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            granter,
            grantee,
            msg_type,
            fees,
        )
    }

    fn assert_eventual_grant(
        &self,
        granter: &str,
        grantee: &str,
        msg_type: &str,
    ) -> Result<(), Error> {
        assert_eventually_succeed(
            &format!("successful grant from granter {granter} to grantee {grantee}"),
            WAIT_GRANT_ATTEMPTS,
            Duration::from_secs(1),
            || {
                query_authz_grant(
                    self.value().chain_id.as_str(),
                    &self.value().command_path,
                    &self.value().home_path,
                    &self.value().rpc_listen_address(),
                    granter,
                    grantee,
                    msg_type,
                )
            },
        )?;

        Ok(())
    }

    fn exec_ibc_transfer_grant<Counterparty>(
        &self,
        granter: &str,
        grantee: &str,
        port: &PortId,
        channel: &ChannelId,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        fees: &str,
    ) -> Result<(), Error> {
        let ibc_transfer_tx = generate_transfer_from_chain_tx(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            granter,
            port.as_ref(),
            channel.as_ref(),
            recipient.value().as_str(),
            &token.value().to_string(),
        )?;

        let ibc_transfer_tx_filename = "ibc-transfer.json";

        self.value()
            .write_file(ibc_transfer_tx_filename, &ibc_transfer_tx)?;

        exec_grant(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            &format!("{}/{ibc_transfer_tx_filename}", self.value().home_path),
            grantee,
            fees,
        )?;

        Ok(())
    }
}
