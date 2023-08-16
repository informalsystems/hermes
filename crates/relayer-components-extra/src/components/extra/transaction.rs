use core::marker::PhantomData;

use ibc_relayer_components::chain::traits::message_sender::MessageSenderComponent;
use ibc_relayer_components::components::default::transaction::DefaultTxComponents;
use ibc_relayer_components::transaction::traits::encode::TxEncoderComponent;
use ibc_relayer_components::transaction::traits::estimate::TxFeeEstimatorComponent;
use ibc_relayer_components::transaction::traits::message_as_tx::MessageAsTxSenderComponent;
use ibc_relayer_components::transaction::traits::nonce::allocate::NonceAllocatorComponent;
use ibc_relayer_components::transaction::traits::nonce::query::NonceQuerierComponent;
use ibc_relayer_components::transaction::traits::response::poll::TxResponsePollerComponent;
use ibc_relayer_components::transaction::traits::response::query::TxResponseQuerierComponent;
use ibc_relayer_components::transaction::traits::submit::TxSubmitterComponent;

pub struct ExtraTxComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_components!(
    [
        MessageSenderComponent,
        MessageAsTxSenderComponent,
        NonceQuerierComponent,
        NonceAllocatorComponent,
        TxEncoderComponent,
        TxFeeEstimatorComponent,
        TxSubmitterComponent,
        TxResponsePollerComponent,
        TxResponseQuerierComponent,
    ],
    ExtraTxComponents<BaseComponents>,
    DefaultTxComponents<BaseComponents>,
);
