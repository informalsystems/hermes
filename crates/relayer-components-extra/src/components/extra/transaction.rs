use core::marker::PhantomData;

use ibc_relayer_components::chain::traits::message_sender::MessageSenderComponent;
use ibc_relayer_components::components::default::transaction::DefaultTxComponents;
use ibc_relayer_components::transaction::traits::message_as_tx::MessageAsTxSenderComponent;
use ibc_relayer_components::transaction::traits::nonce::allocate::NonceAllocatorComponent;
use ibc_relayer_components::transaction::traits::response::poll::TxResponsePollerComponent;

pub struct ExtraTxComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_components!(
    [
        MessageSenderComponent,
        MessageAsTxSenderComponent,
        NonceAllocatorComponent,
        TxResponsePollerComponent,
    ],
    ExtraTxComponents<BaseComponents>,
    DefaultTxComponents<BaseComponents>,
);
