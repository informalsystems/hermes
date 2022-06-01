/*!
   Types for information about a chain wallet.
*/

use core::fmt::{self, Display};
use ibc_relayer::keyring::KeyEntry;

use crate::types::env::{prefix_writer, EnvWriter, ExportEnv};
use crate::types::tagged::*;

/**
   Newtype wrapper for a wallet ID as identified by the chain and relayer.
*/
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct WalletId(pub String);

/**
   Newtype wrapper for the address a wallet corresponds to.
*/
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct WalletAddress(pub String);

/**
   A wallet containing the information about the ID, address,
   and also the public/private key information in the form of
   [KeyEntry](ibc_relayer::keyring::KeyEntry).
*/
#[derive(Debug, Clone)]
pub struct Wallet {
    /// The ID of the wallet for accessing it from the key store.
    pub id: WalletId,

    /// The address for receiving tokens for this wallet.
    pub address: WalletAddress,

    /// The wallet key information in the form of [`KeyEntry`] that
    /// is used by the relayer.
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
#[derive(Debug, Clone)]
pub struct TestWallets {
    /// The validator wallet.
    pub validator: Wallet,

    /// The relayer wallet. This is used by the relayer by default.
    pub relayer: Wallet,

    /// The first user wallet that can be used for testing.
    pub user1: Wallet,

    /// The second user wallet that can be used for testing.
    pub user2: Wallet,
}

/**
   Extra methods for [`Wallet`] that is [tagged](crate::types::tagged).

   This trait is auto implemented for `MonoTagged<Chain, Wallet>` so
   that we can call methods on it directly.
*/
pub trait TaggedWallet<Chain> {
    /// Get the [`WalletId`] tagged with the given `Chain`.
    fn id(&self) -> MonoTagged<Chain, &WalletId>;

    /// Get the [`WalletAddress`] tagged with the given `Chain`.
    fn address(&self) -> MonoTagged<Chain, &WalletAddress>;

    /// Get the [`KeyEntry`] tagged with the given `Chain`.
    fn key(&self) -> MonoTagged<Chain, &KeyEntry>;
}

/**
   Extra methods for [`TestWallets`] that is [tagged](crate::types::tagged).

   This trait is auto implemented for `MonoTagged<Chain, TestWallets>` so
   that we can call methods on it directly.
*/
pub trait TaggedTestWalletsExt<Chain> {
    /// Get the validator [`Wallet`] tagged with the given `Chain`.
    fn validator(&self) -> MonoTagged<Chain, &Wallet>;

    /// Get the relayer [`Wallet`] tagged with the given `Chain`.
    fn relayer(&self) -> MonoTagged<Chain, &Wallet>;

    /// Get the first user [`Wallet`] tagged with the given `Chain`.
    fn user1(&self) -> MonoTagged<Chain, &Wallet>;

    /// Get the second user [`Wallet`] tagged with the given `Chain`.
    fn user2(&self) -> MonoTagged<Chain, &Wallet>;
}

impl Wallet {
    /// Create a new [`Wallet`]
    pub fn new(id: String, address: String, key: KeyEntry) -> Self {
        Self {
            id: WalletId(id),
            address: WalletAddress(address),
            key,
        }
    }
}

impl WalletAddress {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl<Chain> TaggedWallet<Chain> for MonoTagged<Chain, Wallet> {
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

impl<Chain> TaggedTestWalletsExt<Chain> for MonoTagged<Chain, TestWallets> {
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

impl<'a, Chain> TaggedTestWalletsExt<Chain> for MonoTagged<Chain, &'a TestWallets> {
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

impl ExportEnv for TestWallets {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.validator
            .export_env(&mut prefix_writer("VALIDATOR", writer));
        self.relayer
            .export_env(&mut prefix_writer("RELAYER", writer));
        self.user1.export_env(&mut prefix_writer("USER1", writer));
        self.user2.export_env(&mut prefix_writer("USER2", writer));
    }
}

impl ExportEnv for Wallet {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("KEY_ID", &self.id.0);
        writer.write_env("ADDRESS", &self.address.0);
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
