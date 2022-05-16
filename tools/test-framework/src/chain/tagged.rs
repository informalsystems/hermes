/*!
   Methods for tagged version of the chain driver.
*/

use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use serde::Serialize;
use serde_json as json;

use crate::chain::driver::interchain::{
    interchain_submit, query_interchain_account, register_interchain_account,
};
use crate::chain::driver::query_txs::query_recipient_transactions;
use crate::chain::driver::transfer::local_transfer_token;
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::prelude::TaggedConnectionIdRef;
use crate::relayer::transfer::ibc_token_transfer;
use crate::types::id::{TaggedChainIdRef, TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::*;
use crate::types::wallet::{Wallet, WalletAddress};

/**
   A [`ChainDriver`] may be tagged with a `Chain` tag in the form
   [`MonoTagged<Chain, ChainDriver>`].

   It would implement the [`TaggedChainDriverExt`] trait to provide tagged
   version of the chain methods.

   The tagged chain driver methods help ensure that the `ChainDriver`
   methods are used with the values associated to the correct chain.
*/
pub trait TaggedChainDriverExt<Chain> {
    fn chain_id(&self) -> TaggedChainIdRef<Chain>;

    fn tx_config(&self) -> MonoTagged<Chain, &TxConfig>;

    fn send_tx(&self, wallet: &MonoTagged<Chain, &Wallet>, messages: Vec<Any>)
        -> Result<(), Error>;

    /**
       Tagged version of [`ChainDriver::query_balance`].

       Query for the balance of a wallet that belongs to `Chain`
       in the denomination that belongs to `Chain`.
    */
    fn query_balance(
        &self,
        wallet_id: &MonoTagged<Chain, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<u64, Error>;

    /**
       Tagged version of [`ChainDriver::assert_eventual_wallet_amount`].

       Assert that a wallet belongs to `Chain` would reach the target
       amount in the denomination that belongs to `Chain`.
    */
    fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<Chain, &WalletAddress>,
        target_amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error>;

    /**
       Submits an IBC token transfer transaction to `Chain` to any other
       `Counterparty` chain.

       The following parameters are accepted:

       - A `PortId` on `Chain` that corresponds to a channel connected to
         `Counterparty`.

       - A `ChannelId` on `Chain` that corresponds to a channel connected to
         `Counterparty`.

       - The [`Wallet`] of the sender on `Chain`.

       - The [`WalletAddress`] address of the recipient on `Counterparty`.

       - The denomination of the amount on `Chain`.

       - The transfer amount.
    */
    fn ibc_transfer_token<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
        amount: u64,
    ) -> Result<(), Error>;

    fn local_transfer_token(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Chain, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error>;

    /**
        Taggged version of [`query_recipient_transactions`].

        Query for the transactions related to a wallet on `Chain`
        receiving token transfer from others.
    */
    fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<Chain, &WalletAddress>,
    ) -> Result<json::Value, Error>;

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

impl<'a, Chain: Send> TaggedChainDriverExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn chain_id(&self) -> TaggedChainIdRef<Chain> {
        self.map_ref(|val| &val.chain_id)
    }

    fn tx_config(&self) -> MonoTagged<Chain, &TxConfig> {
        self.map_ref(|val| &val.tx_config)
    }

    fn send_tx(
        &self,
        wallet: &MonoTagged<Chain, &Wallet>,
        messages: Vec<Any>,
    ) -> Result<(), Error> {
        self.value().send_tx(wallet.value(), messages)
    }

    fn query_balance(
        &self,
        wallet_id: &MonoTagged<Chain, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<u64, Error> {
        self.value().query_balance(wallet_id.value(), denom.value())
    }

    fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<Chain, &WalletAddress>,
        target_amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error> {
        self.value()
            .assert_eventual_wallet_amount(user.value(), target_amount, denom.value())
    }

    fn ibc_transfer_token<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
        amount: u64,
    ) -> Result<(), Error> {
        self.value().runtime.block_on(ibc_token_transfer(
            &self.tx_config(),
            port_id,
            channel_id,
            sender,
            recipient,
            denom,
            amount,
        ))
    }

    fn local_transfer_token(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Chain, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error> {
        local_transfer_token(
            self.value(),
            sender.value(),
            recipient.value(),
            amount,
            denom.value(),
        )
    }

    fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<Chain, &WalletAddress>,
    ) -> Result<json::Value, Error> {
        query_recipient_transactions(self.value(), recipient_address.value())
    }

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
