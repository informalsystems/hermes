use async_trait::async_trait;

use crate::base::chain::traits::context::ChainContext;
use crate::base::core::traits::sync::Async;
use crate::base::types::aliases::{Event, Message};
use crate::std_prelude::*;

pub trait HasMessageSender: ChainContext {
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
