use serde::Serialize;

use crate::chain::driver::interchain::{
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
        register_interchain_account(self.value(), from.value(), connection_id.value())
    }

    fn query_interchain_account<Counterparty>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
    ) -> Result<MonoTagged<Counterparty, WalletAddress>, Error> {
        query_interchain_account(self.value(), from.value(), connection_id.value())
            .map(MonoTagged::new)
    }

    fn interchain_submit<Counterparty, T: Serialize>(
        &self,
        from: &MonoTagged<Chain, &WalletAddress>,
        connection_id: &TaggedConnectionIdRef<Chain, Counterparty>,
        msg: &T,
    ) -> Result<(), Error> {
        interchain_submit(self.value(), from.value(), connection_id.value(), msg)
    }
}
