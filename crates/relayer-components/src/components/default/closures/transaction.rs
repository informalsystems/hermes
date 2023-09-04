use crate::chain::traits::components::message_sender::CanSendMessages;
use crate::chain::traits::types::chain_id::HasChainId;
use crate::components::default::transaction::DefaultTxComponents;
use crate::core::traits::component::HasComponents;
use crate::core::traits::error::HasErrorType;
use crate::logger::traits::has_logger::HasLogger;
use crate::logger::traits::level::HasBaseLogLevels;
use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::sleep::CanSleep;
use crate::runtime::traits::time::HasTime;
use crate::transaction::components::poll::{CanRaiseNoTxResponseError, HasPollTimeout};
use crate::transaction::traits::components::nonce_querier::NonceQuerier;
use crate::transaction::traits::components::tx_encoder::TxEncoder;
use crate::transaction::traits::components::tx_fee_estimater::TxFeeEstimator;
use crate::transaction::traits::components::tx_response_querier::TxResponseQuerier;
use crate::transaction::traits::components::tx_submitter::TxSubmitter;
use crate::transaction::traits::event::CanParseTxResponseAsEvents;
use crate::transaction::traits::fee::HasFeeForSimulation;
use crate::transaction::traits::logs::nonce::CanLogNonce;
use crate::transaction::traits::nonce::guard::HasNonceGuard;
use crate::transaction::traits::nonce::mutex::HasMutexForNonceAllocation;
use crate::transaction::traits::signer::HasSigner;
use crate::transaction::traits::types::HasTxTypes;

pub trait HasDefaultTxMessageSenderClosure: CanSendMessages {}

impl<Chain, BaseComponents> HasDefaultTxMessageSenderClosure for Chain
where
    Chain: HasErrorType
        + HasTxTypes
        + HasSigner
        + HasNonceGuard
        + HasChainId
        + HasFeeForSimulation
        + HasMutexForNonceAllocation
        + HasPollTimeout
        + HasLogger
        + CanLogNonce
        + CanParseTxResponseAsEvents
        + CanRaiseNoTxResponseError
        + HasComponents<Components = DefaultTxComponents<BaseComponents>>,
    Chain::Runtime: HasMutex + HasTime + CanSleep,
    Chain::Logger: HasBaseLogLevels,
    BaseComponents: TxEncoder<Chain>
        + TxFeeEstimator<Chain>
        + NonceQuerier<Chain>
        + TxSubmitter<Chain>
        + TxResponseQuerier<Chain>,
{
}
