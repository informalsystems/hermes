use crossbeam_channel::{Receiver, Select};

pub struct RecvMultiple<'a, K, T> {
    selector: Select<'a>,
    receivers: &'a [(K, Receiver<T>)],
}

impl<'a, K, T> RecvMultiple<'a, K, T> {
    pub fn new(receivers: &'a [(K, Receiver<T>)]) -> Self {
        // Build a list of operations.
        let mut selector = Select::new();
        for (_, r) in receivers {
            selector.recv(r);
        }

        Self {
            selector,
            receivers,
        }
    }

    pub fn recv_multiple(&mut self) -> Option<(&K, T)> {
        // Complete the selected operation.
        let oper = self.selector.select();
        let index = oper.index();

        // Get the receiver who is ready
        let (k, r) = &self.receivers[index];

        // Receive the message
        let result = oper.recv(r).ok()?;

        Some((k, result))
    }
}
