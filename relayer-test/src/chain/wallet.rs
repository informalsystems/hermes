use ibc_relayer::keyring::KeyEntry;

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
    pub fn new(
        id: String,
        address: String,
        key: KeyEntry,
    ) -> Self {
        Self {
            id: WalletId(id),
            address: WalletAddress(address),
            key,
        }
    }
}
