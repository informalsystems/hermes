use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{
    ChainA, ChainB, ClientIdA, ClientIdB, RelayAToB, RelayBToA, RelayError,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::types::aliases::Runtime;
use crate::full::batch::types::aliases::MessageBatchSender;
use crate::full::runtime::traits::channel::HasChannelTypes;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait RelayAToBWithBatchBuilder<Build>: Async
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType,
    ChainA<Build>: HasRuntime,
    ChainB<Build>: HasRuntime,
    Runtime<ChainA<Build>>: HasChannelTypes + HasChannelOnceTypes,
    Runtime<ChainB<Build>>: HasChannelTypes + HasChannelOnceTypes,
{
    async fn build_relay_a_to_b_with_batch(
        build: &Build,
        src_client_id: &ClientIdA<Build>,
        dst_client_id: &ClientIdB<Build>,
        src_chain: ChainA<Build>,
        dst_chain: ChainB<Build>,
        src_batch_sender: MessageBatchSender<ChainA<Build>, RelayError<Build>>,
        dst_batch_sender: MessageBatchSender<ChainB<Build>, RelayError<Build>>,
    ) -> Result<RelayAToB<Build>, Build::Error>;
}

#[async_trait]
pub trait RelayBToAWithBatchBuilder<Build>: Async
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType,
    ChainA<Build>: HasRuntime,
    ChainB<Build>: HasRuntime,
    Runtime<ChainA<Build>>: HasChannelTypes + HasChannelOnceTypes,
    Runtime<ChainB<Build>>: HasChannelTypes + HasChannelOnceTypes,
{
    async fn build_relay_b_to_a_with_batch(
        build: &Build,
        src_client_id: &ClientIdB<Build>,
        dst_client_id: &ClientIdA<Build>,
        src_chain: ChainB<Build>,
        dst_chain: ChainA<Build>,
        src_batch_sender: MessageBatchSender<ChainB<Build>, RelayError<Build>>,
        dst_batch_sender: MessageBatchSender<ChainA<Build>, RelayError<Build>>,
    ) -> Result<RelayBToA<Build>, Build::Error>;
}
