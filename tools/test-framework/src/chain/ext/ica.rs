use serde::Serialize;

use crate::chain::cli::ica::{
    interchain_submit, query_interchain_account, register_interchain_account,
};
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::prelude::TaggedConnectionIdRef;
use crate::types::tagged::*;
use crate::types::wallet::WalletAddress;

pub trait InterchainAccountMethodsExt<Chain> {
    fn register_interchain_account<Counterparty>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
    ) -> Result<(), Error>;

    fn query_interchain_account<Counterparty>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
    ) -> Result<MonoTagged<Counterparty, WalletAddress>, Error>;

    fn interchain_submit<Counterparty, T: Serialize>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
        msg: &T,
    ) -> Result<(), Error>;
}

impl<'a, Chain: Send> InterchainAccountMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn register_interchain_account<Counterparty>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
    ) -> Result<(), Error> {
        let driver = *self.value();
        register_interchain_account(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            from.value().as_str(),
            connection_id.value().as_str(),
        )
    }

    fn query_interchain_account<Counterparty>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
    ) -> Result<MonoTagged<Counterparty, WalletAddress>, Error> {
        let driver = *self.value();
        let address = query_interchain_account(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            from.value().as_str(),
            connection_id.value().as_str(),
        )?;

        Ok(MonoTagged::new(WalletAddress(address)))
    }

    fn interchain_submit<Counterparty, T: Serialize>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
        msg: &T,
    ) -> Result<(), Error> {
        let driver = *self.value();
        let msg_json = serde_json::to_string_pretty(msg).unwrap();

        interchain_submit(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            from.value().as_str(),
            connection_id.value().as_str(),
            &msg_json,
        )
    }
}
