/*!
   Types for information about a chain wallet.
*/

use core::fmt::{self, Display};
use ibc_relayer::keyring::KeyEntry;

use crate::tagged::mono::Tagged;

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
pub struct ChainWallets {
    pub validator: Wallet,
    pub relayer: Wallet,
    pub user1: Wallet,
    pub user2: Wallet,
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

impl<'a, Chain> Tagged<Chain, &'a Wallet> {
    pub fn id<'b>(&'b self) -> Tagged<Chain, &'b WalletId> {
        self.map_ref(|w| &w.id)
    }

    pub fn address<'b>(&'b self) -> Tagged<Chain, &'b WalletAddress> {
        self.map_ref(|w| &w.address)
    }

    pub fn key<'b>(&'b self) -> Tagged<Chain, &'b KeyEntry> {
        self.map_ref(|w| &w.key)
    }
}

impl<'a, Chain> Tagged<Chain, &'a ChainWallets> {
    pub fn validator(&self) -> Tagged<Chain, &Wallet> {
        self.map_ref(|w| &w.validator)
    }

    pub fn relayer(&self) -> Tagged<Chain, &Wallet> {
        self.map_ref(|w| &w.relayer)
    }

    pub fn user1(&self) -> Tagged<Chain, &Wallet> {
        self.map_ref(|w| &w.user1)
    }

    pub fn user2(&self) -> Tagged<Chain, &Wallet> {
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
