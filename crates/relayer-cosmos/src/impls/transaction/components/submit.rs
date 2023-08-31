use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::TxRaw;
use ibc_relayer::chain::cosmos::tx::broadcast_tx_sync;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer_components::transaction::traits::submit::TxSubmitter;
use tendermint::Hash as TxHash;

use crate::contexts::transaction::CosmosTxContext;
use crate::impls::transaction::component::CosmosTxComponents;
use crate::types::error::{BaseError, Error};

#[async_trait]
impl TxSubmitter<CosmosTxContext> for CosmosTxComponents {
    async fn submit_tx(context: &CosmosTxContext, tx: &SignedTx) -> Result<TxHash, Error> {
        let data = encode_tx_raw(tx)?;

        let tx_config = &context.tx_config;
        let rpc_client = &context.rpc_client;

        let response = broadcast_tx_sync(rpc_client, &tx_config.rpc_address, data)
            .await
            .map_err(BaseError::relayer)?;

        if response.code.is_err() {
            return Err(BaseError::check_tx(response).into());
        }

        Ok(response.hash)
    }
}

fn encode_tx_raw(signed_tx: &SignedTx) -> Result<Vec<u8>, Error> {
    let tx_raw = TxRaw {
        body_bytes: signed_tx.body_bytes.clone(),
        auth_info_bytes: signed_tx.auth_info_bytes.clone(),
        signatures: signed_tx.signatures.clone(),
    };

    let mut tx_bytes = Vec::new();
    prost::Message::encode(&tx_raw, &mut tx_bytes).map_err(BaseError::encode)?;

    Ok(tx_bytes)
}
