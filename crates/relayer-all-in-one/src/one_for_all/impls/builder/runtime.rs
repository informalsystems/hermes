use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<Builder> HasRuntime for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    type Runtime = OfaRuntimeWrapper<Builder::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.builder.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Builder::Error {
        Builder::runtime_error(e)
    }
}
