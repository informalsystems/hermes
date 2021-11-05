/*!
   Types for information about a chain wallet.
*/

use core::fmt::{self, Display};
use ibc_relayer::keyring::KeyEntry;

use crate::types::tagged::*;

/**
   Newtype wrapper for a wallet ID as identified by the chain and relayer.
*/
#[derive(Debug)]
pub struct WalletId(pub String);

/**
   Newtype wrapper for the address a wallet corresponds to.
*/
#[derive(Debug)]
pub struct WalletAddress(pub String);

/**
   A wallet containing the information about the ID, address,
   and also the public/private key information in the form of
   [KeyEntry](ibc_relayer::keyring::KeyEntry).
*/
#[derive(Debug)]
pub struct Wallet {
    pub id: WalletId,
    pub address: WalletAddress,
    pub key: KeyEntry,
}

/**
   A collection of wallets used for testing. We use an explicit
   struct instead of a generic HashMap so that the retrieval
   of a specific wallet can always succeed. We shouldn't need
   more than the wallets listed here for testing purposes.

   In case we do need more wallets for testing, there shouldn't
   be much overhead for adding a few more wallets here globally.
   Alternatively the particular test that needs more wallets
   can add new wallets in the test itself, or we can add
   a HashMap here together with a
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   trait to generate additional wallets during test setup.
*/
#[derive(Debug)]
pub struct TestWallets {
    pub validator: Wallet,
    pub relayer: Wallet,
    pub user1: Wallet,
    pub user2: Wallet,
}

pub trait TaggedWallet<Chain> {
    fn id(&self) -> MonoTagged<Chain, &WalletId>;

    fn address(&self) -> MonoTagged<Chain, &WalletAddress>;

    fn key(&self) -> MonoTagged<Chain, &KeyEntry>;
}

pub trait TaggedTestWallets<Chain> {
    fn validator(&self) -> MonoTagged<Chain, &Wallet>;

    fn relayer(&self) -> MonoTagged<Chain, &Wallet>;

    fn user1(&self) -> MonoTagged<Chain, &Wallet>;

    fn user2(&self) -> MonoTagged<Chain, &Wallet>;
}

impl Wallet {
    pub fn new(id: String, address: String, key: KeyEntry) -> Self {
        Self {
            id: WalletId(id),
            address: WalletAddress(address),
            key,
        }
    }
}

impl<'a, Chain> TaggedWallet<Chain> for MonoTagged<Chain, &'a Wallet> {
    fn id(&self) -> MonoTagged<Chain, &WalletId> {
        self.map_ref(|w| &w.id)
    }

    fn address(&self) -> MonoTagged<Chain, &WalletAddress> {
        self.map_ref(|w| &w.address)
    }

    fn key(&self) -> MonoTagged<Chain, &KeyEntry> {
        self.map_ref(|w| &w.key)
    }
}

impl<'a, Chain> TaggedTestWallets<Chain> for MonoTagged<Chain, &'a TestWallets> {
    fn validator(&self) -> MonoTagged<Chain, &Wallet> {
        self.map_ref(|w| &w.validator)
    }

    fn relayer(&self) -> MonoTagged<Chain, &Wallet> {
        self.map_ref(|w| &w.relayer)
    }

    fn user1(&self) -> MonoTagged<Chain, &Wallet> {
        self.map_ref(|w| &w.user1)
    }

    fn user2(&self) -> MonoTagged<Chain, &Wallet> {
        self.map_ref(|w| &w.user2)
    }
}

impl Display for WalletId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Display for WalletAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
