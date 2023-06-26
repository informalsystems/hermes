use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;
use ibc_relayer_components_extra::runtime::traits::channel::{
    CanCreateChannels, CanStreamReceiver, CanUseChannels,
};
use ibc_relayer_components_extra::runtime::traits::spawn::HasSpawner;

pub trait AfoRuntime:
    HasMutex + CanSleep + HasTime + HasSpawner + CanCreateChannels + CanStreamReceiver + CanUseChannels
{
}

impl<Runtime> AfoRuntime for Runtime where
    Runtime: HasMutex
        + CanSleep
        + HasTime
        + HasSpawner
        + CanCreateChannels
        + CanStreamReceiver
        + CanUseChannels
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
