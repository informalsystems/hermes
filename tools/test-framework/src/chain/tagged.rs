/*!
   Methods for tagged version of the chain driver.
*/
use eyre::eyre;
use serde_json as json;

use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::config::compat_mode::CompatMode;
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint_rpc::client::{Client, HttpClient};
use tendermint_rpc::Url;
use tracing::warn;

use crate::chain::cli::query::query_auth_module;
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
       Tagged version of [`ChainDriver::assert_eventual_escrowed_amount_ics29`].

       Assert that a wallet should eventually have escrowed the amount for ICS29
       fees of a given denomination.
       Legacy ICS29 will escrow recv_fee + ack_fee + timeout_fee while more recent
       versions will escrow max(recv_fee + ack_fee, timeout_fee).
    */
    fn assert_eventual_escrowed_amount_ics29(
        &self,
        user: &MonoTagged<Chain, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        recv_fee: u128,
        ack_fee: u128,
        timeout_fee: u128,
    ) -> Result<(), Error>;

    /**
        Tagged version of [`query_recipient_transactions`].

        Query for the transactions related to a wallet on `Chain`
        receiving token transfer from others.
    */
    fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<Chain, &WalletAddress>,
    ) -> Result<json::Value, Error>;

    /**
       Tagged version of [`query_auth_module`].

        Query for the authority account for a specific module.
    */
    fn query_auth_module(&self, module_name: &str) -> Result<String, Error>;
}

impl<Chain: Send> TaggedChainDriverExt<Chain> for MonoTagged<Chain, &ChainDriver> {
    fn chain_id(&self) -> TaggedChainIdRef<Chain> {
        self.map_ref(|val| &val.chain_id)
    }

    fn tx_config(&self) -> MonoTagged<Chain, &TxConfig> {
        self.map_ref(|val| &val.tx_config)
    }

    fn rpc_client(&self) -> Result<MonoTagged<Chain, HttpClient>, Error> {
        let rpc_address = self.value().tx_config.rpc_address.clone();
        let rt = &self.value().runtime;

        let mut client = HttpClient::new(rpc_address.clone()).map_err(handle_generic_error)?;

        let compat_mode = rt.block_on(fetch_compat_mode(
            &client,
            &self.value().chain_id,
            &rpc_address,
            &self.value().compat_mode,
        ))?;

        client.set_compat_mode(compat_mode);

        Ok(MonoTagged::new(client))
    }

    fn send_tx(
        &self,
        wallet: &MonoTagged<Chain, &Wallet>,
        messages: Vec<Any>,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let rpc_client = self.rpc_client()?;

        let key = &wallet
            .value()
            .key
            .downcast()
            .ok_or_else(|| eyre!("unable to downcast key"))
            .map_err(Error::generic)?;
        self.value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client.as_ref().into_value(),
                &self.value().tx_config,
                key,
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

    fn assert_eventual_escrowed_amount_ics29(
        &self,
        user: &MonoTagged<Chain, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        recv_fee: u128,
        ack_fee: u128,
        timeout_fee: u128,
    ) -> Result<(), Error> {
        self.value().assert_eventual_escrowed_amount_ics29(
            user.value(),
            token.value(),
            recv_fee,
            ack_fee,
            timeout_fee,
        )
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

    fn query_auth_module(&self, module_name: &str) -> Result<String, Error> {
        let driver = *self.value();
        query_auth_module(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            module_name,
        )
    }
}

pub async fn fetch_compat_mode(
    client: &HttpClient,
    id: &ChainId,
    rpc_addr: &Url,
    configured_mode: &Option<CompatMode>,
) -> Result<CompatMode, Error> {
    use ibc_relayer::chain::cosmos::query::fetch_version_specs;
    use ibc_relayer::util::compat_mode::compat_mode_from_node_version;
    use ibc_relayer::util::compat_mode::compat_mode_from_version_specs;

    let version_specs = fetch_version_specs(id, client, rpc_addr).await;

    let compat_mode = match version_specs {
        Ok(specs) => compat_mode_from_version_specs(configured_mode, specs.consensus),
        Err(e) => {
            warn!("Failed to fetch version specs for chain '{id}': {e}");

            let status = client.status().await.map_err(handle_generic_error)?;

            warn!(
                "Will fall back on using the node version: {}",
                status.node_info.version
            );

            compat_mode_from_node_version(configured_mode, status.node_info.version)
        }
    }?;

    Ok(compat_mode)
}
