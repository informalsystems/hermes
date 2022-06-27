pub struct MessageSenderWithUpdateClient<Sender> {
    pub sender: Sender,
}

impl<'a, Sender> MessageSenderWithUpdateClient<Sender> {
    pub fn new(sender: Sender) -> Self {
        Self { sender }
    }
}
