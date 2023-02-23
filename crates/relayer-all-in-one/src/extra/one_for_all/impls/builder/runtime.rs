use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::extra::one_for_all::traits::builder::OfaFullBuilder;
use crate::extra::one_for_all::types::builder::OfaFullBuilderWrapper;

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
