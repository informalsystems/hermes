#[derive(Clone)]
pub struct OfaRuntimeWrapper<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaRuntimeWrapper<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }
}

pub enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}
