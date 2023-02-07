use crate::base::runtime::traits::log::HasBasicLogger;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::base::runtime::traits::time::HasTime;

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
