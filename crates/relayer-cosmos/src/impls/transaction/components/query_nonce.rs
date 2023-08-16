use async_trait::async_trait;
use ibc_relayer::chain::cosmos::query::account::query_account;
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer::keyring::{Secp256k1KeyPair, SigningKeyPair};
use ibc_relayer_components::transaction::traits::nonce::query::NonceQuerier;

use crate::contexts::transaction::CosmosTxContext;
use crate::impls::transaction::component::CosmosTxComponents;
use crate::types::error::{BaseError, Error};

#[async_trait]
impl NonceQuerier<CosmosTxContext> for CosmosTxComponents {
    async fn query_nonce(
        context: &CosmosTxContext,
        key_pair: &Secp256k1KeyPair,
    ) -> Result<Account, Error> {
        let tx_config = &context.tx_config;
        let address = key_pair.account();

        let account = query_account(&tx_config.grpc_address, &address)
            .await
            .map_err(BaseError::relayer)?;

        Ok(account.into())
    }
}
