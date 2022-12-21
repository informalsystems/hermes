use alloc::sync::Arc;

pub struct OfaTxWrapper<TxContext> {
    pub tx_context: Arc<TxContext>,
}

impl<TxContext> OfaTxWrapper<TxContext> {
    pub fn new(tx_context: TxContext) -> Self {
        Self {
            tx_context: Arc::new(tx_context),
        }
    }
}

impl<TxContext> Clone for OfaTxWrapper<TxContext> {
    fn clone(&self) -> Self {
        Self {
            tx_context: self.tx_context.clone(),
        }
    }
}
