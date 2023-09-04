use async_trait::async_trait;

use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

pub struct MessageAsTxSenderComponent;

#[async_trait]
pub trait MessageAsTxSender<TxContext>
where
    TxContext: HasTxTypes,
{
    async fn send_messages_as_tx(
        context: &TxContext,
        signer: &TxContext::Signer,
        nonce: &TxContext::Nonce,
        messages: &[TxContext::Message],
    ) -> Result<TxContext::TxResponse, TxContext::Error>;
}

#[async_trait]
impl<TxContext, Component> MessageAsTxSender<TxContext> for Component
where
    TxContext: HasTxTypes,
    Component: DelegateComponent<MessageAsTxSenderComponent>,
    Component::Delegate: MessageAsTxSender<TxContext>,
{
    async fn send_messages_as_tx(
        context: &TxContext,
        signer: &TxContext::Signer,
        nonce: &TxContext::Nonce,
        messages: &[TxContext::Message],
    ) -> Result<TxContext::TxResponse, TxContext::Error> {
        Component::Delegate::send_messages_as_tx(context, signer, nonce, messages).await
    }
}

#[async_trait]
pub trait CanSendMessagesAsTx: HasTxTypes {
    async fn send_messages_as_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        messages: &[Self::Message],
    ) -> Result<Self::TxResponse, Self::Error>;
}

#[async_trait]
impl<TxContext> CanSendMessagesAsTx for TxContext
where
    TxContext: HasTxTypes + HasComponents,
    TxContext::Components: MessageAsTxSender<TxContext>,
{
    async fn send_messages_as_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        messages: &[Self::Message],
    ) -> Result<Self::TxResponse, Self::Error> {
        TxContext::Components::send_messages_as_tx(self, signer, nonce, messages).await
    }
}
