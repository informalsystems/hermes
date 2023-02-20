use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::one_for_all::traits::builder::OfaFullBuilder;
use crate::full::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder> HasRuntime for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
{
    type Runtime = OfaRuntimeWrapper<Builder::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.builder.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Builder::Error {
        Builder::runtime_error(e)
    }
}
