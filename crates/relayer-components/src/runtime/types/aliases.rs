use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;

pub type Runtime<Context> = <Context as HasRuntime>::Runtime;

pub type Mutex<Context, T> = <Runtime<Context> as HasMutex>::Mutex<T>;
