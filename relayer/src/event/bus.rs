use std::collections::VecDeque;

use crossbeam_channel as channel;

pub struct EventBus<T> {
    txs: VecDeque<channel::Sender<T>>,
}

impl<T> Default for EventBus<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> EventBus<T> {
    pub fn new() -> Self {
        Self {
            txs: VecDeque::new(),
        }
    }

    pub fn subscribe(&mut self) -> channel::Receiver<T> {
        let (tx, rx) = channel::unbounded();
        self.txs.push_back(tx);
        rx
    }

    pub fn broadcast(&self, value: T) -> Result<(), channel::SendError<T>>
    where
        T: Clone,
    {
        // TODO: Avoid cloning when sending to last subscriber
        for tx in &self.txs {
            tx.send(value.clone())?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::EventBus;

    use serial_test::serial;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use test_env_log::test;

    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn counter() -> usize {
        COUNTER.load(Ordering::SeqCst)
    }

    fn reset_counter() {
        COUNTER.store(0, Ordering::SeqCst);
    }

    fn incr_counter() {
        COUNTER.fetch_add(1, Ordering::SeqCst);
    }

    #[derive(Debug, PartialEq, Eq)]
    pub struct Value(u32);

    impl Clone for Value {
        fn clone(&self) -> Self {
            incr_counter();
            Self(self.0)
        }
    }

    #[test]
    #[serial]
    fn single_subscribers() {
        reset_counter();

        let mut bus = EventBus::new();
        let rx = bus.subscribe();

        bus.broadcast(Value(42)).unwrap();
        bus.broadcast(Value(113)).unwrap();

        assert_eq!(rx.recv(), Ok(Value(42)));
        assert_eq!(rx.recv(), Ok(Value(113)));
        assert_eq!(counter(), 2);
    }

    #[test]
    #[serial]
    fn multi_subscribers() {
        reset_counter();

        let mut bus = EventBus::new();

        let n = 10;
        let mut rxs = vec![];

        for _i in 0..n {
            rxs.push(bus.subscribe());
        }

        bus.broadcast(Value(42)).unwrap();
        bus.broadcast(Value(113)).unwrap();

        for rx in rxs {
            assert_eq!(rx.recv(), Ok(Value(42)));
            assert_eq!(rx.recv(), Ok(Value(113)));
        }

        assert_eq!(counter(), 20);
    }
}
