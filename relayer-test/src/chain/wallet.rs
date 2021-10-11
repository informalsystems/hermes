#[derive(Debug)]
pub struct WalletId(pub String);

#[derive(Debug)]
pub struct WalletAddress(pub String);

#[derive(Debug)]
pub struct Wallet {
    pub id: WalletId,
    pub address: WalletAddress,
}

impl Wallet {
    pub fn new(
        id: String,
        address: String
    ) -> Self {
        Self {
            id: WalletId(id),
            address: WalletAddress(address)
        }
    }
}
