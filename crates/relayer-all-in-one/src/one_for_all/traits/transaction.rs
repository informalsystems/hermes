use core::fmt::{Debug, Display};
use core::time::Duration;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::logger::traits::logger::BaseLogger;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;

use crate::all_for_one::runtime::AfoRuntime;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaTxContext: Async {
    type Error: Async + Debug;

    type Runtime: AfoRuntime;

    type Logger: HasBaseLogLevels;

    type ChainId: Display + Eq + Ord + Async;

    /**
       Corresponds to
       [`HasMessageType::Message`](ibc_relayer_components::chain::traits::types::message::HasMessageType::Message).
    */
    type Message: Async;

    /**
       Corresponds to
       [`HasEventType::Event`](ibc_relayer_components::chain::traits::types::event::HasEventType::Event).
    */
    type Event: Async;

    type Transaction: Async;

    type Nonce: Async;

    type Fee: Async;

    type Signer: Async;

    type TxHash: Async;

    type TxResponse: Async;

    fn runtime(&self) -> &Self::Runtime;

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Self::Error;

    fn logger(&self) -> &Self::Logger;

    fn log_nonce<'a>(event: &'a Self::Nonce) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn tx_no_response_error(tx_hash: &Self::TxHash) -> Self::Error;

    fn tx_size(tx: &Self::Transaction) -> usize;

    fn chain_id(&self) -> &Self::ChainId;

    fn get_signer(&self) -> &Self::Signer;

    fn fee_for_simulation(&self) -> &Self::Fee;

    fn poll_timeout(&self) -> Duration;

    fn poll_backoff(&self) -> Duration;

    async fn encode_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        fee: &Self::Fee,
        messages: &[Self::Message],
    ) -> Result<Self::Transaction, Self::Error>;

    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<Self::TxHash, Self::Error>;

    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Self::Fee, Self::Error>;

    async fn query_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Option<Self::TxResponse>, Self::Error>;

    async fn query_nonce(&self, signer: &Self::Signer) -> Result<Self::Nonce, Self::Error>;

    fn mutex_for_nonce_allocation(
        &self,
        signer: &Self::Signer,
    ) -> &<Self::Runtime as HasMutex>::Mutex<()>;

    fn parse_tx_response_as_events(
        response: Self::TxResponse,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;
}
