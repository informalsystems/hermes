use namada_sdk::wallet::{LoadStoreError, Wallet, WalletIo, WalletStorage};
use signature::rand_core::OsRng;

#[derive(Debug, Clone)]
pub(super) struct NullWalletUtils;

impl WalletIo for NullWalletUtils {
    type Rng = OsRng;
}

impl WalletStorage for NullWalletUtils {
    fn save<U>(&self, _wallet: &Wallet<U>) -> Result<(), LoadStoreError> {
        Ok(())
    }

    fn load<U>(&self, _wallet: &mut Wallet<U>) -> Result<(), LoadStoreError> {
        Ok(())
    }
}
