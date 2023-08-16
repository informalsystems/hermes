use core::marker::PhantomData;

use ibc_relayer_components::chain::traits::message_sender::MessageSenderComponent;
use ibc_relayer_components::components::default::transaction::DefaultTxComponents;
use ibc_relayer_components::transaction::traits::nonce::allocate::NonceAllocatorComponent;

pub struct ExtraTxComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_components!(
    [NonceAllocatorComponent, MessageSenderComponent,],
    ExtraTxComponents<BaseComponents>,
    DefaultTxComponents<BaseComponents>,
);
