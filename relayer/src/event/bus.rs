use crossbeam_channel as channel;

pub struct EventBus<T> {
    txs: Vec<channel::Sender<T>>,
}

impl<T> Default for EventBus<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> EventBus<T> {
    pub fn new() -> Self {
        Self { txs: vec![] }
    }

    pub fn subscribe(&mut self) -> channel::Receiver<T> {
        let (tx, rx) = channel::unbounded();
        self.txs.push(tx);
        rx
    }

    pub fn broadcast(&self, value: T)
    where
        T: Clone,
    {
        for tx in &self.txs {
            tx.send(value.clone()).unwrap();
        }
    }
}
