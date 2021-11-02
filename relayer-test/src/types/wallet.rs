use ibc_relayer::keyring::KeyEntry;

use crate::tagged::mono::Tagged;

#[derive(Debug)]
pub struct WalletId(pub String);

#[derive(Debug)]
pub struct WalletAddress(pub String);

#[derive(Debug)]
pub struct Wallet {
    pub id: WalletId,
    pub address: WalletAddress,
    pub key: KeyEntry,
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
