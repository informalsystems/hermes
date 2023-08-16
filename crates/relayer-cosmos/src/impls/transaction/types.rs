use alloc::sync::Arc;
use futures::lock::MutexGuard;
use ibc_proto::cosmos::tx::v1beta1::{Fee, TxRaw};
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainIdType;
use ibc_relayer_components::chain::traits::types::event::HasEventType;
use ibc_relayer_components::chain::traits::types::message::HasMessageType;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::has_logger::HasLoggerType;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::transaction::traits::nonce::guard::HasNonceGuard;
use ibc_relayer_components::transaction::traits::types::{HasNonceType, HasSignerType, HasTxTypes};
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use prost::Message;
use tendermint::abci::Event as AbciEvent;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;

use crate::contexts::transaction::CosmosTxContext;
use crate::traits::message::CosmosMessage;
use crate::types::error::{BaseError, Error};

impl HasErrorType for CosmosTxContext {
    type Error = Error;
}

impl HasRuntime for CosmosTxContext {
    type Runtime = TokioRuntimeContext;

    fn runtime(&self) -> &TokioRuntimeContext {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }
}

impl HasLoggerType for CosmosTxContext {
    type Logger = TracingLogger;
}

impl HasChainIdType for CosmosTxContext {
    type ChainId = ChainId;
}

impl HasMessageType for CosmosTxContext {
    type Message = Arc<dyn CosmosMessage>;
}

impl HasEventType for CosmosTxContext {
    type Event = Arc<AbciEvent>;
}

impl HasSignerType for CosmosTxContext {
    type Signer = Secp256k1KeyPair;
}

impl HasNonceType for CosmosTxContext {
    type Nonce = Account;
}

impl HasNonceGuard for CosmosTxContext {
    type NonceGuard<'a> = (MutexGuard<'a, ()>, Account);

    fn deref_nonce<'a, 'b>((_, nonce): &'a Self::NonceGuard<'b>) -> &'a Account {
        nonce
    }
}

impl HasTxTypes for CosmosTxContext {
    type Transaction = SignedTx;

    type Fee = Fee;

    type TxHash = TxHash;

    type TxResponse = TxResponse;

    fn tx_size(signed_tx: &SignedTx) -> usize {
        let tx_raw = TxRaw {
            body_bytes: signed_tx.body_bytes.clone(),
            auth_info_bytes: signed_tx.auth_info_bytes.clone(),
            signatures: signed_tx.signatures.clone(),
        };

        tx_raw.encoded_len()
    }
}
