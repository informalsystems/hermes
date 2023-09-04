use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;
use ibc_relayer_components_extra::runtime::traits::channel::{
    CanCloneSender, CanCreateChannels, CanStreamReceiver, CanUseChannels, HasChannelTypes,
};
use ibc_relayer_components_extra::runtime::traits::channel_once::{
    CanCreateChannelsOnce, CanUseChannelsOnce, HasChannelOnceTypes,
};
use ibc_relayer_components_extra::runtime::traits::spawn::HasSpawner;

pub trait AfoRuntime:
    Clone
    + HasMutex
    + CanSleep
    + HasTime
    + HasSpawner
    + HasChannelTypes
    + HasChannelOnceTypes
    + CanCreateChannels
    + CanCreateChannelsOnce
    + CanStreamReceiver
    + CanCloneSender
    + CanUseChannels
    + CanUseChannelsOnce
{
}

impl<Runtime> AfoRuntime for Runtime where
    Runtime: Clone
        + HasMutex
        + CanSleep
        + HasTime
        + HasSpawner
        + HasChannelTypes
        + HasChannelOnceTypes
        + CanCreateChannels
        + CanCreateChannelsOnce
        + CanStreamReceiver
        + CanCloneSender
        + CanUseChannels
        + CanUseChannelsOnce
{
}

pub trait HasAfoRuntime: HasRuntime<Runtime = Self::AfoRuntime> {
    type AfoRuntime: AfoRuntime;
}

impl<Context, Runtime> HasAfoRuntime for Context
where
    Context: HasRuntime<Runtime = Runtime>,
    Runtime: AfoRuntime,
{
    type AfoRuntime = Runtime;
}
