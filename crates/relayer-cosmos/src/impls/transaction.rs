use core::time::Duration;

use alloc::sync::Arc;
use async_trait::async_trait;
use futures::lock::Mutex;
use ibc_proto::cosmos::tx::v1beta1::{Fee, Tx, TxRaw};
use ibc_relayer::chain::cosmos::encode::{key_pair_to_signer, sign_tx};
use ibc_relayer::chain::cosmos::gas::gas_amount_to_fee;
use ibc_relayer::chain::cosmos::query::account::query_account;
use ibc_relayer::chain::cosmos::query::tx::query_tx_response;
use ibc_relayer::chain::cosmos::simulate::send_tx_simulate;
use ibc_relayer::chain::cosmos::tx::broadcast_tx_sync;
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::config::types::Memo;
use ibc_relayer::keyring::{Secp256k1KeyPair, SigningKeyPair};
use ibc_relayer_all_in_one::one_for_all::traits::transaction::OfaTxContext;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::log::value::LogValue;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use prost::Message as _;
use tendermint::abci::Event as AbciEvent;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;

use crate::contexts::transaction::CosmosTxContext;
use crate::traits::message::CosmosMessage;
use crate::types::error::{BaseError, Error};

#[async_trait]
impl OfaTxContext for CosmosTxContext {
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type ChainId = ChainId;

    type Message = Arc<dyn CosmosMessage>;

    type Event = Arc<AbciEvent>;

    type Transaction = SignedTx;

    type Nonce = Account;

    type Fee = Fee;

    type Signer = Secp256k1KeyPair;

    type TxHash = TxHash;

    type TxResponse = TxResponse;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
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

    fn tx_no_response_error(tx_hash: &TxHash) -> Error {
        BaseError::tx_no_response(*tx_hash).into()
    }

    fn tx_size(signed_tx: &SignedTx) -> usize {
        let tx_raw = TxRaw {
            body_bytes: signed_tx.body_bytes.clone(),
            auth_info_bytes: signed_tx.auth_info_bytes.clone(),
            signatures: signed_tx.signatures.clone(),
        };

        tx_raw.encoded_len()
    }

    fn chain_id(&self) -> &ChainId {
        &self.tx_config.chain_id
    }

    fn get_signer(&self) -> &Secp256k1KeyPair {
        &self.key_entry
    }

    fn fee_for_simulation(&self) -> &Fee {
        &self.tx_config.gas_config.max_fee
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
        messages: &[Arc<dyn CosmosMessage>],
    ) -> Result<SignedTx, Error> {
        let tx_config = &self.tx_config;
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

    async fn submit_tx(&self, tx: &SignedTx) -> Result<TxHash, Error> {
        let data = encode_tx_raw(tx)?;

        let tx_config = &self.tx_config;
        let rpc_client = &self.rpc_client;

        let response = broadcast_tx_sync(rpc_client, &tx_config.rpc_address, data)
            .await
            .map_err(BaseError::relayer)?;

        if response.code.is_err() {
            return Err(BaseError::check_tx(response).into());
        }

        Ok(response.hash)
    }

    async fn estimate_tx_fee(&self, tx: &SignedTx) -> Result<Fee, Error> {
        let tx = Tx {
            body: Some(tx.body.clone()),
            auth_info: Some(tx.auth_info.clone()),
            signatures: tx.signatures.clone(),
        };

        let tx_config = &self.tx_config;

        let response = send_tx_simulate(&tx_config.grpc_address, tx)
            .await
            .map_err(BaseError::relayer)?;

        let gas_info = response
            .gas_info
            .ok_or_else(BaseError::missing_simulate_gas_info)?;

        let fee = gas_amount_to_fee(&tx_config.gas_config, gas_info.gas_used);

        Ok(fee)
    }

    async fn query_tx_response(&self, tx_hash: &TxHash) -> Result<Option<TxResponse>, Error> {
        let tx_config = &self.tx_config;
        let rpc_client = &self.rpc_client;

        let response = query_tx_response(rpc_client, &tx_config.rpc_address, tx_hash)
            .await
            .map_err(BaseError::relayer)?;

        Ok(response)
    }

    async fn query_nonce(&self, key_pair: &Secp256k1KeyPair) -> Result<Account, Error> {
        let tx_config = &self.tx_config;
        let address = key_pair.account();

        let account = query_account(&tx_config.grpc_address, &address)
            .await
            .map_err(BaseError::relayer)?;

        Ok(account.into())
    }

    fn mutex_for_nonce_allocation(&self, _signer: &Secp256k1KeyPair) -> &Mutex<()> {
        &self.nonce_mutex
    }

    fn parse_tx_response_as_events(
        response: TxResponse,
    ) -> Result<Vec<Vec<Arc<AbciEvent>>>, Error> {
        let events = split_events_by_messages(response.tx_result.events);

        Ok(events)
    }
}

fn split_events_by_messages(in_events: Vec<AbciEvent>) -> Vec<Vec<Arc<AbciEvent>>> {
    let mut out_events = Vec::new();
    let mut current_events = Vec::new();
    let mut first_message_event_found = false;

    for event in in_events.into_iter() {
        // TODO: What is the purpose of this filter ?
        // It seems that the event kind "message" from the Tx Response of some chains
        // only have 1 event attribute:
        // event kind: message
        // event attributes: [
        // EventAttribute {
        //    key: "sender",
        //   value: "cosmos1w2jl4lt77j0u3wuvknmrflp9pmwx5zmrr2j8x7",
        //  index: true,
        // },
        // ]
        // But others have multiple event attributes:
        // event kind in send_message: message
        // event.attributes: [
        // EventAttribute {
        // key: "action",
        //  value: "/ibc.core.channel.v1.MsgAcknowledgement",
        //   index: true,
        // },
        // EventAttribute {
        //   key: "sender",
        //   value: "cosmos1zl89j8asalm9s7gd5spskxtmh4l49lzs86auqx",
        //   index: true,
        // },
        // ]
        //
        //if event.kind == "message"
        //    && event.attributes.len() == 1
        //    && &event.attributes[0].key == "action"

        if event.kind == "message" && event.attributes.iter().any(|attr| attr.key == "action") {
            if first_message_event_found {
                out_events.push(current_events);
            } else {
                first_message_event_found = true;
            }

            current_events = vec![Arc::new(event)];
        } else if first_message_event_found {
            current_events.push(Arc::new(event));
        }
    }

    if !current_events.is_empty() {
        out_events.push(current_events);
    }

    out_events
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
