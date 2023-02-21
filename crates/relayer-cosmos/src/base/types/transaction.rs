use alloc::sync::Arc;
use tokio::sync::Mutex;

pub struct CosmosTxWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub nonce_mutex: Mutex<()>,
}

impl<Chain> CosmosTxWrapper<Chain> {
    pub fn new(chain: Arc<Chain>) -> Self {
        Self {
            chain,
            nonce_mutex: Mutex::new(()),
        }
    }
}
