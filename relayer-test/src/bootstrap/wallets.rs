use crate::chain::wallet::Wallet;
use crate::tagged::mono::Tagged;

pub struct ChainWallets {
    pub validator: Wallet,
    pub relayer: Wallet,
    pub user1: Wallet,
    pub user2: Wallet,
}

impl<Chain> Tagged<Chain, ChainWallets> {
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
