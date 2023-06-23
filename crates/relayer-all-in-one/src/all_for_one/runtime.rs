use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;

pub trait AfoRuntime: HasMutex + CanSleep + HasTime {}

impl<Runtime> AfoRuntime for Runtime where Runtime: HasMutex + CanSleep + HasTime {}

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
