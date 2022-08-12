use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::traits::message_channel::OnceChannelContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::IbcEvent;

#[async_trait]
pub trait MessageResultChannel<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type Sender: Async;
    type Receiver: Async;

    async fn send_ok(
        sender: Self::Sender,
        result: Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>,
    );

    async fn send_error(sender: Self::Sender, err: Relay::Error);

    async fn receive_result(
        receiver: Self::Receiver,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>;
}

#[async_trait]
impl<Relay, Target, Channel> MessageResultChannel<Relay, Target> for Channel
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
    >,
    Relay::Error: From<Channel::Error>,
{
    type Sender = Channel::Sender;
    type Receiver = Channel::Receiver;

    async fn send_ok(
        sender: Self::Sender,
        result: Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>,
    ) {
        let _ = Channel::send_once(sender, Ok(result)).await;
    }

    async fn send_error(sender: Self::Sender, err: Relay::Error) {
        let _ = Channel::send_once(sender, Err(err)).await;
    }

    async fn receive_result(
        receiver: Self::Receiver,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>
    {
        Channel::receive_once(receiver).await?
    }
}
