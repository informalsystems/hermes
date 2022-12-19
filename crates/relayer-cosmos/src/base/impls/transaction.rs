use async_trait::async_trait;
use core::time::Duration;
use ibc_proto::cosmos::tx::v1beta1::{Fee, TxRaw};
use ibc_relayer::chain::cosmos::encode::{key_pair_to_signer, sign_tx};
use ibc_relayer::chain::cosmos::gas::gas_amount_to_fee;
use ibc_relayer::chain::cosmos::simulate::send_tx_simulate;
use ibc_relayer::chain::cosmos::tx::broadcast_tx_sync;
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::config::types::Memo;
use ibc_relayer::keyring::Secp256k1KeyPair;
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

    type Nonce = Account;

    type Fee = Fee;

    type Signer = Secp256k1KeyPair;

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
        self.chain.key_entry()
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
        key_pair: &Secp256k1KeyPair,
        account: &Account,
        fee: &Fee,
        messages: &[CosmosIbcMessage],
    ) -> Result<SignedTx, Error> {
        let tx_config = self.chain.tx_config();
        let memo = Memo::default();
        let signer = key_pair_to_signer(key_pair).map_err(Error::relayer)?;

        let raw_messages = messages
            .into_iter()
            .map(|message| (message.to_protobuf_fn)(&signer).map_err(Error::encode))
            .collect::<Result<Vec<_>, _>>()?;

        let signed_tx = sign_tx(tx_config, key_pair, account, &memo, &raw_messages, fee)
            .map_err(Error::relayer)?;

        Ok(signed_tx)
    }

    async fn submit_tx(&self, tx: &SignedTx) -> Result<TxHash, Error> {
        let tx_config = self.chain.tx_config();

        let response = broadcast_tx_sync(&tx_config.rpc_client, &tx_config.rpc_address, tx.clone())
            .await
            .map_err(Error::relayer)?;

        Ok(response.hash)
    }

    async fn estimate_tx_fee(&self, tx: &SignedTx) -> Result<Fee, Error> {
        let tx_config = self.chain.tx_config();

        let response = send_tx_simulate(&tx_config.grpc_address, tx.clone())
            .await
            .map_err(Error::relayer)?;

        let gas_info = response
            .gas_info
            .ok_or_else(Error::missing_simulate_gas_info)?;

        let fee = gas_amount_to_fee(&tx_config.gas_config, gas_info.gas_used);

        Ok(fee)
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
