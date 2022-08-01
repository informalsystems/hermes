use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::message_channel::{HasChannelContext, ReceiverOnceContext, SenderOnceContext};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::IbcEvent;

#[async_trait]
pub trait MessageResultSender<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    async fn send_ok(
        self,
        result: Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>,
    );

    async fn send_error(self, err: Relay::Error);
}

#[async_trait]
pub trait MessageResultReceiver<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    async fn receive_result(
        self,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>;
}

#[async_trait]
impl<Relay, Target, Channel, Sender> MessageResultSender<Relay, Target> for Sender
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Sender: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: SenderOnceContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = Sender,
    >,
{
    async fn send_ok(
        self,
        result: Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>,
    ) {
        let _ = Channel::send_once(self, Ok(result)).await;
    }

    async fn send_error(self, err: Relay::Error) {
        let _ = Channel::send_once(self, Err(err)).await;
    }
}

#[async_trait]
impl<Relay, Target, Channel, Receiver> MessageResultReceiver<Relay, Target> for Receiver
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Receiver: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: ReceiverOnceContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Receiver = Receiver,
    >,
    Relay::Error: From<Channel::Error>,
{
    async fn receive_result(
        self,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>
    {
        Channel::receive_once(self).await?
    }
}
