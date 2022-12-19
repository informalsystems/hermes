use async_trait::async_trait;
use core::time::Duration;
use ibc_proto::cosmos::tx::v1beta1::{Fee, SignerInfo, TxRaw};
use ibc_relayer::chain::cosmos::types::account::AccountSequence;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer_framework::base::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use prost::Message as _;
use tendermint::abci::Event;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tokio::sync::Mutex;

use crate::base::error::Error;
use crate::base::traits::chain::CosmosChain;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::message::CosmosIbcMessage;

impl<Chain> OfaTxTypes for CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Message = CosmosIbcMessage;

    type Event = Event;

    type Transaction = SignedTx;

    type Nonce = AccountSequence;

    type Fee = Fee;

    type Signer = SignerInfo;

    type TxHash = TxHash;

    type TxResponse = TxResponse;
}

#[async_trait]
impl<Chain> OfaTxContext for CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime> {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        Error::tokio(e)
    }

    fn tx_no_response_error(tx_hash: &TxHash) -> Self::Error {
        Error::tx_no_response(tx_hash.clone())
    }

    fn tx_size(signed_tx: &Self::Transaction) -> usize {
        let tx_raw = TxRaw {
            body_bytes: signed_tx.body_bytes.clone(),
            auth_info_bytes: signed_tx.auth_info_bytes.clone(),
            signatures: signed_tx.signatures.clone(),
        };

        tx_raw.encoded_len()
    }

    fn get_signer(&self) -> &Self::Signer {
        todo!()
    }

    fn fee_for_simulation(&self) -> &Self::Fee {
        &self.chain.tx_config().gas_config.max_fee
    }

    fn poll_timeout(&self) -> Duration {
        Duration::from_secs(300)
    }

    fn poll_backoff(&self) -> Duration {
        Duration::from_secs(1)
    }

    async fn encode_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        fee: &Self::Fee,
        messages: &[Self::Message],
    ) -> Result<Self::Transaction, Error> {
        todo!()
    }

    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<TxHash, Error> {
        todo!()
    }

    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Fee, Error> {
        todo!()
    }

    async fn query_tx_response(&self, tx_hash: &TxHash) -> Result<Option<TxResponse>, Error> {
        todo!()
    }

    async fn query_nonce(&self, signer: &Self::Signer) -> Result<Self::Nonce, Error> {
        todo!()
    }

    fn mutex_for_nonce_allocation(&self, signer: &Self::Signer) -> &Mutex<()> {
        todo!()
    }

    fn parse_tx_response_as_events(response: TxResponse) -> Result<Vec<Vec<Event>>, Error> {
        todo!()
    }
}
