use core::time::Duration;

use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::transaction::impls::nonces::naive::HasMutexForNonceAllocation;
use crate::base::transaction::impls::poll::HasPollTimeout;
use crate::base::transaction::traits::fee::HasFeeForSimulation;
use crate::base::transaction::traits::signer::HasSigner;

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
