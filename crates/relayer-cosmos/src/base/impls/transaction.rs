use core::time::Duration;

use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::{Fee, TxRaw};
use ibc_relayer::chain::cosmos::encode::{key_pair_to_signer, sign_tx};
use ibc_relayer::chain::cosmos::event::split_events_by_messages;
use ibc_relayer::chain::cosmos::gas::gas_amount_to_fee;
use ibc_relayer::chain::cosmos::query::account::query_account;
use ibc_relayer::chain::cosmos::query::tx::query_tx_response;
use ibc_relayer::chain::cosmos::simulate::send_tx_simulate;
use ibc_relayer::chain::cosmos::tx::broadcast_tx_sync;
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::config::types::Memo;
use ibc_relayer::keyring::{Secp256k1KeyPair, SigningKeyPair};
use ibc_relayer_all_in_one::base::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_runtime::tokio::logger::value::LogValue;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use prost::Message as _;
use tendermint::abci::Event;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tokio::sync::Mutex;
use tracing::info;

use crate::base::error::{BaseError, Error};
use crate::base::traits::chain::CosmosChain;
use crate::base::types::message::CosmosIbcMessage;
use crate::base::types::transaction::CosmosTxWrapper;

impl<Chain> OfaTxTypes for CosmosTxWrapper<Chain>
where
    Chain: CosmosChain,
{
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type ChainId = ChainId;

    type Message = CosmosIbcMessage;

    type Event = Event;

    type Transaction = SignedTx;

    type Nonce = Account;

    type Fee = Fee;

    type Signer = Secp256k1KeyPair;

    type TxHash = TxHash;

    type TxResponse = TxResponse;
}

#[async_trait]
impl<Chain> OfaTxContext for CosmosTxWrapper<Chain>
where
    Chain: CosmosChain,
{
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime> {
        self.chain.runtime()
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }

    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }

    fn log_nonce(nonce: &Account) -> LogValue<'_> {
        LogValue::Debug(nonce)
    }

    fn tx_no_response_error(tx_hash: &TxHash) -> Self::Error {
        BaseError::tx_no_response(*tx_hash).into()
    }

    fn tx_size(signed_tx: &Self::Transaction) -> usize {
        let tx_raw = TxRaw {
            body_bytes: signed_tx.body_bytes.clone(),
            auth_info_bytes: signed_tx.auth_info_bytes.clone(),
            signatures: signed_tx.signatures.clone(),
        };

        tx_raw.encoded_len()
    }

    fn chain_id(&self) -> &Self::ChainId {
        &self.chain.tx_config().chain_id
    }

    fn get_signer(&self) -> &Self::Signer {
        self.chain.key_entry()
    }

    fn fee_for_simulation(&self) -> &Self::Fee {
        &self.chain.tx_config().gas_config.max_fee
    }

    fn poll_timeout(&self) -> Duration {
        Duration::from_secs(300)
    }

    fn poll_backoff(&self) -> Duration {
        Duration::from_millis(200)
    }

    async fn encode_tx(
        &self,
        key_pair: &Secp256k1KeyPair,
        account: &Account,
        fee: &Fee,
        messages: &[CosmosIbcMessage],
    ) -> Result<SignedTx, Error> {
        let tx_config = self.chain.tx_config();
        let memo = Memo::default();
        let signer = key_pair_to_signer(key_pair).map_err(BaseError::relayer)?;

        let raw_messages = messages
            .iter()
            .map(|message| (message.to_protobuf_fn)(&signer).map_err(BaseError::encode))
            .collect::<Result<Vec<_>, _>>()?;

        let signed_tx = sign_tx(tx_config, key_pair, account, &memo, &raw_messages, fee)
            .map_err(BaseError::relayer)?;

        Ok(signed_tx)
    }

    async fn submit_tx(&self, tx: &SignedTx) -> Result<TxHash, Error> {
        let tx_config = self.chain.tx_config();

        let response = broadcast_tx_sync(&tx_config.rpc_client, &tx_config.rpc_address, tx.clone())
            .await
            .map_err(BaseError::relayer)?;

        if response.code.is_err() {
            return Err(BaseError::check_tx(response).into());
        }

        Ok(response.hash)
    }

    async fn estimate_tx_fee(&self, tx: &SignedTx) -> Result<Fee, Error> {
        let tx_config = self.chain.tx_config();

        let response = send_tx_simulate(&tx_config.grpc_address, tx.clone())
            .await
            .map_err(BaseError::relayer)?;

        let gas_info = response
            .gas_info
            .ok_or_else(BaseError::missing_simulate_gas_info)?;

        let fee = gas_amount_to_fee(&tx_config.gas_config, gas_info.gas_used);

        Ok(fee)
    }

    async fn query_tx_response(&self, tx_hash: &TxHash) -> Result<Option<TxResponse>, Error> {
        let tx_config = self.chain.tx_config();

        let response = query_tx_response(&tx_config.rpc_client, &tx_config.rpc_address, tx_hash)
            .await
            .map_err(BaseError::relayer)?;

        Ok(response)
    }

    async fn query_nonce(&self, key_pair: &Secp256k1KeyPair) -> Result<Account, Error> {
        let tx_config = self.chain.tx_config();
        let address = key_pair.account();

        let account = query_account(&tx_config.grpc_address, &address)
            .await
            .map_err(BaseError::relayer)?;

        Ok(account.into())
    }

    fn mutex_for_nonce_allocation(&self, _signer: &Self::Signer) -> &Mutex<()> {
        &self.nonce_mutex
    }

    fn parse_tx_response_as_events(response: TxResponse) -> Result<Vec<Vec<Event>>, Error> {
        let events = split_events_by_messages(response.tx_result.events);

        Ok(events)
    }
}
