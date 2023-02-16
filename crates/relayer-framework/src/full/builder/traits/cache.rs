use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{ChainA, ChainB, ChainIdA, ChainIdB, RelayError};
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::types::aliases::{Mutex, Runtime};
use crate::full::batch::types::aliases::MessageBatchSender;
use crate::full::runtime::traits::channel::HasChannelTypes;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;

pub trait HasChainABatchSenderCache: HasBiRelayType + HasRuntimeWithMutex
where
    ChainA<Self>: HasRuntime,
    Runtime<ChainA<Self>>: HasChannelTypes + HasChannelOnceTypes,
{
    fn batch_sender_cache(&self) -> &ChainABatchSenderCache<Self>;
}

pub trait HasChainBBatchSenderCache: HasBiRelayType + HasRuntimeWithMutex
where
    ChainB<Self>: HasRuntime,
    Runtime<ChainB<Self>>: HasChannelTypes + HasChannelOnceTypes,
{
    fn batch_sender_cache(&self) -> &ChainBBatchSenderCache<Self>;
}

pub type ChainABatchSenderCache<Build> = Arc<
    Mutex<
        Build,
        BTreeMap<
            (ChainIdA<Build>, ChainIdB<Build>),
            MessageBatchSender<ChainA<Build>, RelayError<Build>>,
        >,
    >,
>;

pub type ChainBBatchSenderCache<Build> = Arc<
    Mutex<
        Build,
        BTreeMap<
            (ChainIdB<Build>, ChainIdA<Build>),
            MessageBatchSender<ChainB<Build>, RelayError<Build>>,
        >,
    >,
>;
