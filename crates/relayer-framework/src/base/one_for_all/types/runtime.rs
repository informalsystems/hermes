use alloc::sync::Arc;

pub enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

pub struct OfaRuntimeWrapper<Runtime> {
    pub runtime: Arc<Runtime>,
}

impl<Runtime> OfaRuntimeWrapper<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self {
            runtime: Arc::new(runtime),
        }
    }
}

impl<Runtime> Clone for OfaRuntimeWrapper<Runtime> {
    fn clone(&self) -> Self {
        Self {
            runtime: self.runtime.clone(),
        }
    }
}
