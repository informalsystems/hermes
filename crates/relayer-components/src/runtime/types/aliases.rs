use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::runtime::HasRuntime;

pub type Runtime<Context> = <Context as HasRuntime>::Runtime;

pub type Mutex<Context, T> = <Runtime<Context> as HasMutex>::Mutex<T>;
