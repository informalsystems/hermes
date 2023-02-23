use core::time::Duration;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::transaction::impls::nonces::naive::HasMutexForNonceAllocation;
use ibc_relayer_components::transaction::impls::poll::HasPollTimeout;
use ibc_relayer_components::transaction::traits::fee::HasFeeForSimulation;
use ibc_relayer_components::transaction::traits::signer::HasSigner;

impl<TxContext> HasSigner for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn get_signer(&self) -> &Self::Signer {
        self.tx_context.get_signer()
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
