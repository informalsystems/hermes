use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_relayer::chain::cosmos::encode::{key_pair_to_signer, sign_tx};
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::config::types::Memo;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_components::transaction::traits::components::tx_encoder::TxEncoder;

use crate::contexts::transaction::CosmosTxContext;
use crate::impls::transaction::component::CosmosTxComponents;
use crate::traits::message::CosmosMessage;
use crate::types::error::{BaseError, Error};

#[async_trait]
impl TxEncoder<CosmosTxContext> for CosmosTxComponents {
    async fn encode_tx(
        context: &CosmosTxContext,
        key_pair: &Secp256k1KeyPair,
        account: &Account,
        fee: &Fee,
        messages: &[Arc<dyn CosmosMessage>],
    ) -> Result<SignedTx, Error> {
        let tx_config = &context.tx_config;
        let memo = Memo::default();
        let signer = key_pair_to_signer(key_pair).map_err(BaseError::relayer)?;

        let raw_messages = messages
            .iter()
            .map(|message| message.encode_protobuf(&signer).map_err(BaseError::encode))
            .collect::<Result<Vec<_>, _>>()?;

        let signed_tx = sign_tx(tx_config, key_pair, account, &memo, &raw_messages, fee)
            .map_err(BaseError::relayer)?;

        Ok(signed_tx)
    }
}
