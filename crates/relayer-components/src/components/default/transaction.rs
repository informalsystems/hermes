use core::marker::PhantomData;

use crate::chain::traits::message_sender::MessageSenderComponent;
use crate::transaction::impls::message_sender::SendMessagesAsTx;
use crate::transaction::impls::nonces::mutex::AllocateNonceWithMutex;
use crate::transaction::traits::nonce::allocate::NonceAllocatorComponent;

pub struct DefaultTxComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    MessageSenderComponent,
    DefaultTxComponents<BaseComponents>,
    SendMessagesAsTx,
);

crate::delegate_component!(
    NonceAllocatorComponent,
    DefaultTxComponents<BaseComponents>,
    AllocateNonceWithMutex,
);
