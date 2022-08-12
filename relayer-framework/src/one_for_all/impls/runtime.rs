use crate::one_for_all::impls::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::traits::contexts::error::HasError;

pub struct OfaHasRuntime<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaHasRuntime<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }
}

impl<Runtime: OfaRuntime> HasError for OfaHasRuntime<Runtime> {
    type Error = OfaErrorContext<Runtime::Error>;
}
