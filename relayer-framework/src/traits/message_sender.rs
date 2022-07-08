use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::chain_context::ChainContext;
use crate::traits::core::Async;
use crate::types::aliases::{Event, Message};

pub trait MessageSenderContext: ChainContext {
    type MessageSender: MessageSender<Self>;
}

#[async_trait]
pub trait MessageSender<Context>: Async
where
    Context: ChainContext,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message<Context>>,
    ) -> Result<Vec<Vec<Event<Context>>>, Context::Error>;
}
