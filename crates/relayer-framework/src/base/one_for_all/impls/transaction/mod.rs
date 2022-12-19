use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;
use core::time::Duration;

use crate::base::chain::traits::message_sender::{CanSendMessages, MessageSender};
use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::transaction::impls::message_sender::SendMessagesAsTx;
use crate::base::transaction::impls::nonces::naive::{
    HasMutexForNonceAllocation, NaiveNonceAllocator,
};
use crate::base::transaction::impls::poll::{
    HasPollTimeout, InjectNoTxResponseError, PollTxResponse,
};
use crate::base::transaction::traits::encode::CanEncodeTx;
use crate::base::transaction::traits::estimate::CanEstimateTxFee;
use crate::base::transaction::traits::event::CanParseTxResponseAsEvents;
use crate::base::transaction::traits::fee::HasFeeForSimulation;
use crate::base::transaction::traits::message::{CanSendMessagesAsTx, MessageAsTxSender};
use crate::base::transaction::traits::nonce::{CanAllocateNonce, CanQueryNonce, NonceAllocator};
use crate::base::transaction::traits::response::{
    CanPollTxResponse, CanQueryTxResponse, TxResponsePoller,
};
use crate::base::transaction::traits::signer::HasSigner;
use crate::base::transaction::traits::submit::CanSubmitTx;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

impl<TxContext> HasErrorType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxTypes,
{
    type Error = TxContext::Error;
}

impl<TxContext> HasRuntime for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Runtime = OfaRuntimeWrapper<TxContext::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.tx_context.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Self::Error {
        TxContext::runtime_error(e)
    }
}

impl<TxContext> HasMessageType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxTypes,
{
    type Message = TxContext::Message;
}

impl<TxContext> HasEventType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxTypes,
{
    type Event = TxContext::Event;
}

impl<TxContext> HasTxTypes for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Transaction = TxContext::Transaction;

    type Nonce = TxContext::Nonce;

    type Fee = TxContext::Fee;

    type Signer = TxContext::Signer;

    type TxHash = TxContext::TxHash;

    type TxResponse = TxContext::TxResponse;

    fn tx_size(tx: &Self::Transaction) -> usize {
        TxContext::tx_size(tx)
    }
}

impl<TxContext> HasSigner for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn get_signer(&self) -> &Self::Signer {
        self.tx_context.get_signer()
    }
}

#[async_trait]
impl<TxContext> CanEncodeTx for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn encode_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        fee: &Self::Fee,
        messages: &[Self::Message],
    ) -> Result<Self::Transaction, Self::Error> {
        self.tx_context
            .encode_tx(signer, nonce, fee, messages)
            .await
    }
}

#[async_trait]
impl<TxContext> CanSubmitTx for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<Self::TxHash, Self::Error> {
        self.tx_context.submit_tx(tx).await
    }
}

#[async_trait]
impl<TxContext> CanEstimateTxFee for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Self::Fee, Self::Error> {
        self.tx_context.estimate_tx_fee(tx).await
    }
}

#[async_trait]
impl<TxContext> CanQueryTxResponse for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn query_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Option<Self::TxResponse>, Self::Error> {
        self.tx_context.query_tx_response(tx_hash).await
    }
}

#[async_trait]
impl<TxContext> CanQueryNonce for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn query_nonce(&self, signer: &Self::Signer) -> Result<Self::Nonce, Self::Error> {
        self.tx_context.query_nonce(signer).await
    }
}

impl<TxContext> HasFeeForSimulation for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn fee_for_simulation(&self) -> &Self::Fee {
        self.tx_context.fee_for_simulation()
    }
}

#[async_trait]
impl<TxContext> HasMutexForNonceAllocation for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn mutex_for_nonce_allocation(
        &self,
        signer: &Self::Signer,
    ) -> &<Self::Runtime as HasMutex>::Mutex<()> {
        self.tx_context.mutex_for_nonce_allocation(signer)
    }
}

#[async_trait]
impl<TxContext> CanAllocateNonce for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn with_allocated_nonce<'a, R, Cont>(
        &'a self,
        signer: &'a Self::Signer,
        cont: &'a Cont,
    ) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
    where
        R: Async + 'a,
        Cont: Fn(Self::Nonce) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
            + Send
            + Sync
            + 'a,
    {
        NaiveNonceAllocator::with_allocated_nonce(self, signer, cont)
    }
}

impl<TxContext> HasPollTimeout for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn poll_timeout(&self) -> Duration {
        self.tx_context.poll_timeout()
    }

    fn poll_backoff(&self) -> Duration {
        self.tx_context.poll_backoff()
    }
}

impl<TxContext> InjectNoTxResponseError for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn tx_no_response_error(tx_hash: &Self::TxHash) -> Self::Error {
        TxContext::tx_no_response_error(tx_hash)
    }
}

#[async_trait]
impl<TxContext> CanPollTxResponse for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn poll_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Self::TxResponse, Self::Error> {
        PollTxResponse::poll_tx_response(self, tx_hash).await
    }
}

#[async_trait]
impl<TxContext> CanSendMessagesAsTx for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn send_messages_as_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        messages: &[Self::Message],
    ) -> Result<Self::TxResponse, Self::Error> {
        SendMessagesAsTx::send_messages_as_tx(self, signer, nonce, messages).await
    }
}

impl<TxContext> CanParseTxResponseAsEvents for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn parse_tx_response_as_events(
        response: Self::TxResponse,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error> {
        TxContext::parse_tx_response_as_events(response)
    }
}

#[async_trait]
impl<TxContext> CanSendMessages for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error> {
        SendMessagesAsTx::send_messages(self, messages).await
    }
}
