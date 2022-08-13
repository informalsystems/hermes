use crate::one_for_all::impls::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::traits::contexts::error::HasError;

pub struct OfaRuntimeContext<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaRuntimeContext<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }
}

impl<Runtime: OfaRuntime> HasError for OfaRuntimeContext<Runtime> {
    type Error = OfaErrorContext<Runtime::Error>;
}
