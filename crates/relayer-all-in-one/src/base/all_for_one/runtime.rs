use ibc_relayer_components::runtime::traits::log::HasBasicLogger;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;

pub trait AfoBaseRuntime: HasBasicLogger + HasMutex + CanSleep + HasTime {}

impl<Runtime> AfoBaseRuntime for Runtime where
    Runtime: HasBasicLogger + HasMutex + CanSleep + HasTime
{
}

pub trait HasAfoBaseRuntime: HasRuntime<Runtime = Self::AfoBaseRuntime> {
    type AfoBaseRuntime: AfoBaseRuntime;
}

impl<Context, Runtime> HasAfoBaseRuntime for Context
where
    Context: HasRuntime<Runtime = Runtime>,
    Runtime: AfoBaseRuntime,
{
    type AfoBaseRuntime = Runtime;
}
