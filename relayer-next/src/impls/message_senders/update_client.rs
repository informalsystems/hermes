pub struct MessageSenderWithUpdateClient<'a, Sender> {
    pub sender: &'a Sender,
}

impl<'a, Sender> MessageSenderWithUpdateClient<'a, Sender> {
    pub fn new(sender: &'a Sender) -> Self {
        Self { sender }
    }
}
