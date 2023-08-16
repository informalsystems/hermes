use core::marker::PhantomData;

use crate::chain::traits::message_sender::MessageSenderComponent;
use crate::transaction::components::message_as_tx::EstimateFeesAndSendTx;
use crate::transaction::components::message_sender::send_as_tx::SendMessagesAsTx;
use crate::transaction::components::nonce::mutex::AllocateNonceWithMutex;
use crate::transaction::traits::message_as_tx::MessageAsTxSenderComponent;
use crate::transaction::traits::nonce::allocate::NonceAllocatorComponent;

pub struct DefaultTxComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    MessageSenderComponent,
    DefaultTxComponents<BaseComponents>,
    SendMessagesAsTx,
);

crate::delegate_component!(
    MessageAsTxSenderComponent,
    DefaultTxComponents<BaseComponents>,
    EstimateFeesAndSendTx,
);

crate::delegate_component!(
    NonceAllocatorComponent,
    DefaultTxComponents<BaseComponents>,
    AllocateNonceWithMutex,
);
