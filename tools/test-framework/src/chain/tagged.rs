/*!
   Methods for tagged version of the chain driver.
*/

use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::event::IbcEventWithHeight;
use serde_json as json;
use tendermint_rpc::client::{Client, CompatMode, HttpClient};

use crate::chain::cli::query::query_recipient_transactions;
use crate::chain::driver::ChainDriver;
use crate::error::{handle_generic_error, Error};
use crate::ibc::denom::Denom;
use crate::ibc::token::{TaggedDenomExt, TaggedToken, TaggedTokenRef};
use crate::types::id::TaggedChainIdRef;
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

    /// Sets up an RPC client for making requests to the chain node.
    ///
    /// The RPC server must be running and be able to respond on the
    /// `/status` endpoint.
    fn rpc_client(&self) -> Result<MonoTagged<Chain, HttpClient>, Error>;

    fn send_tx(
        &self,
        wallet: &MonoTagged<Chain, &Wallet>,
        messages: Vec<Any>,
    ) -> Result<Vec<IbcEventWithHeight>, Error>;

    /**
       Tagged version of [`ChainDriver::query_balance`].

       Query for the balance of a wallet that belongs to `Chain`
       in the denomination that belongs to `Chain`.
    */
    fn query_balance(
        &self,
        wallet_id: &MonoTagged<Chain, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<TaggedToken<Chain>, Error>;

    /**
       Tagged version of [`ChainDriver::assert_eventual_wallet_amount`].

       Assert that a wallet belongs to `Chain` would reach the target
       amount in the denomination that belongs to `Chain`.
    */
    fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<Chain, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
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
}

impl<'a, Chain: Send> TaggedChainDriverExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn chain_id(&self) -> TaggedChainIdRef<Chain> {
        self.map_ref(|val| &val.chain_id)
    }

    fn tx_config(&self) -> MonoTagged<Chain, &TxConfig> {
        self.map_ref(|val| &val.tx_config)
    }

    fn rpc_client(&self) -> Result<MonoTagged<Chain, HttpClient>, Error> {
        let rpc_address = self.value().tx_config.rpc_address.clone();
        let rt = &self.value().runtime;

        let mut client = HttpClient::new(rpc_address).map_err(handle_generic_error)?;

        let status = rt.block_on(client.status()).map_err(handle_generic_error)?;
        let compat_mode =
            CompatMode::from_version(status.node_info.version).map_err(handle_generic_error)?;
        client.set_compat_mode(compat_mode);

        Ok(MonoTagged::new(client))
    }

    fn send_tx(
        &self,
        wallet: &MonoTagged<Chain, &Wallet>,
        messages: Vec<Any>,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let rpc_client = self.rpc_client()?;

        self.value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client.as_ref().into_value(),
                &self.value().tx_config,
                &wallet.value().key,
                messages,
            ))
            .map_err(Error::relayer)
    }

    fn query_balance(
        &self,
        wallet_id: &MonoTagged<Chain, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<TaggedToken<Chain>, Error> {
        let balance = self
            .value()
            .query_balance(wallet_id.value(), denom.value())?;
        Ok(denom.with_amount(balance))
    }

    fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<Chain, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error> {
        self.value()
            .assert_eventual_wallet_amount(user.value(), token.value())
    }

    fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<Chain, &WalletAddress>,
    ) -> Result<json::Value, Error> {
        let driver = *self.value();
        query_recipient_transactions(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.rpc_listen_address(),
            &recipient_address.value().0,
        )
    }
}
