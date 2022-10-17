use async_trait::async_trait;

use crate::base::chain::traits::types::HasChainTypes;
use crate::base::chain::types::aliases::{Event, Message};
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasMessageSender: HasChainTypes {
    type MessageSender: MessageSender<Self>;
}

#[async_trait]
pub trait MessageSender<Context>: Async
where
    Context: HasChainTypes,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message<Context>>,
    ) -> Result<Vec<Vec<Event<Context>>>, Context::Error>;
}
