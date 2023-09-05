use async_trait::async_trait;

use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;
use crate::transaction::traits::nonce::guard::HasNonceGuard;
use crate::transaction::traits::types::HasSignerType;

pub struct NonceAllocatorComponent;

#[async_trait]
pub trait NonceAllocator<TxContext>
where
    TxContext: HasNonceGuard + HasSignerType + HasErrorType,
{
    async fn allocate_nonce<'a>(
        context: &'a TxContext,
        signer: &'a TxContext::Signer,
    ) -> Result<TxContext::NonceGuard<'a>, TxContext::Error>;
}

#[async_trait]
impl<TxContext, Component> NonceAllocator<TxContext> for Component
where
    TxContext: HasNonceGuard + HasSignerType + HasErrorType,
    Component: DelegateComponent<NonceAllocatorComponent>,
    Component::Delegate: NonceAllocator<TxContext>,
{
    async fn allocate_nonce<'a>(
        context: &'a TxContext,
        signer: &'a TxContext::Signer,
    ) -> Result<TxContext::NonceGuard<'a>, TxContext::Error> {
        Component::Delegate::allocate_nonce(context, signer).await
    }
}

#[async_trait]
pub trait CanAllocateNonce: HasNonceGuard + HasSignerType + HasErrorType {
    async fn allocate_nonce<'a>(
        &'a self,
        signer: &'a Self::Signer,
    ) -> Result<Self::NonceGuard<'a>, Self::Error>;
}

#[async_trait]
impl<TxContext> CanAllocateNonce for TxContext
where
    TxContext: HasNonceGuard + HasSignerType + HasErrorType + HasComponents,
    TxContext::Components: NonceAllocator<TxContext>,
{
    async fn allocate_nonce<'a>(
        &'a self,
        signer: &'a TxContext::Signer,
    ) -> Result<TxContext::NonceGuard<'a>, TxContext::Error> {
        TxContext::Components::allocate_nonce(self, signer).await
    }
}
