use std::path::PathBuf;
use std::{env, fs};

use namada_sdk::wallet::fs::FsWalletStorage;
use namada_sdk::wallet::{LoadStoreError, Store, Wallet, WalletIo, WalletStorage};
use namada_sdk::zeroize::Zeroizing;
use signature::rand_core::OsRng;

/// Wallet utils for Namada context
#[derive(Clone)]
pub(super) struct NullWalletUtils;

impl WalletIo for NullWalletUtils {
    type Rng = OsRng;
}

// Namada wallet never accesses the storage. It reads the keys added in the bootstrap from the store.
impl WalletStorage for NullWalletUtils {
    fn save<U>(&self, _wallet: &Wallet<U>) -> Result<(), LoadStoreError> {
        Ok(())
    }

    fn load<U>(&self, _wallet: &mut Wallet<U>) -> Result<(), LoadStoreError> {
        Ok(())
    }
}

/// For Namada wallet for adding a key with a password
#[derive(Clone)]
pub struct CliWalletUtils {
    store_dir: PathBuf,
}

impl CliWalletUtils {
    pub fn new(store_dir: PathBuf) -> Wallet<Self> {
        Wallet::new(Self { store_dir }, Store::default())
    }
}

impl FsWalletStorage for CliWalletUtils {
    fn store_dir(&self) -> &PathBuf {
        &self.store_dir
    }
}

impl WalletIo for CliWalletUtils {
    type Rng = OsRng;

    fn read_password(_confirm: bool, _target_key: Option<&str>) -> Zeroizing<String> {
        match env::var("NAMADA_WALLET_PASSWORD_FILE") {
            Ok(path) => Zeroizing::new(
                fs::read_to_string(path).expect("Something went wrong reading the file"),
            ),
            Err(_) => match env::var("NAMADA_WALLET_PASSWORD") {
                Ok(password) => Zeroizing::new(password),
                Err(_) => {
                    let prompt = "Enter your decryption password: ";
                    rpassword::read_password_from_tty(Some(prompt))
                        .map(Zeroizing::new)
                        .expect("Failed reading password from tty.")
                }
            },
        }
    }
}
