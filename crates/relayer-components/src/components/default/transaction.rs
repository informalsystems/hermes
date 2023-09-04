use core::marker::PhantomData;

use crate::chain::traits::components::message_sender::MessageSenderComponent;
use crate::transaction::components::message_as_tx::EstimateFeesAndSendTx;
use crate::transaction::components::message_sender::send_as_tx::SendMessagesAsTx;
use crate::transaction::components::nonce::mutex::AllocateNonceWithMutex;
use crate::transaction::components::poll::PollTxResponse;
use crate::transaction::traits::components::message_as_tx_sender::MessageAsTxSenderComponent;
use crate::transaction::traits::components::nonce_allocater::NonceAllocatorComponent;
use crate::transaction::traits::components::nonce_querier::NonceQuerierComponent;
use crate::transaction::traits::components::tx_encoder::TxEncoderComponent;
use crate::transaction::traits::components::tx_fee_estimater::TxFeeEstimatorComponent;
use crate::transaction::traits::components::tx_response_poller::TxResponsePollerComponent;
use crate::transaction::traits::components::tx_response_querier::TxResponseQuerierComponent;
use crate::transaction::traits::components::tx_submitter::TxSubmitterComponent;

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

crate::delegate_component!(
    TxResponsePollerComponent,
    DefaultTxComponents<BaseComponents>,
    PollTxResponse,
);

crate::delegate_components!(
    [
        NonceQuerierComponent,
        TxEncoderComponent,
        TxFeeEstimatorComponent,
        TxSubmitterComponent,
        TxResponseQuerierComponent,
    ],
    DefaultTxComponents<BaseComponents>,
    BaseComponents,
);
