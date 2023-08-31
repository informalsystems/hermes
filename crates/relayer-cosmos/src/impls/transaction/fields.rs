use core::time::Duration;
use futures::lock::Mutex;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::transaction::components::poll::HasPollTimeout;
use ibc_relayer_components::transaction::traits::fee::HasFeeForSimulation;
use ibc_relayer_components::transaction::traits::nonce::mutex::HasMutexForNonceAllocation;
use ibc_relayer_components::transaction::traits::signer::HasSigner;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::contexts::transaction::CosmosTxContext;

impl HasChainId for CosmosTxContext {
    fn chain_id(&self) -> &ChainId {
        &self.tx_config.chain_id
    }
}

impl HasSigner for CosmosTxContext {
    fn get_signer(&self) -> &Secp256k1KeyPair {
        &self.key_entry
    }
}

impl HasFeeForSimulation for CosmosTxContext {
    fn fee_for_simulation(&self) -> &Fee {
        &self.tx_config.gas_config.max_fee
    }
}

impl HasPollTimeout for CosmosTxContext {
    fn poll_timeout(&self) -> Duration {
        Duration::from_secs(300)
    }

    fn poll_backoff(&self) -> Duration {
        Duration::from_millis(200)
    }
}

impl HasMutexForNonceAllocation for CosmosTxContext {
    fn mutex_for_nonce_allocation(&self, _signer: &Secp256k1KeyPair) -> &Mutex<()> {
        &self.nonce_mutex
    }

    fn mutex_to_nonce_guard<'a>(
        mutex_guard: <Self::Runtime as HasMutex>::MutexGuard<'a, ()>,
        nonce: Self::Nonce,
    ) -> Self::NonceGuard<'a> {
        (mutex_guard, nonce)
    }
}
