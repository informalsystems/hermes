use crate::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components::core::traits::error::HasErrorType;

impl<Runtime: OfaBaseRuntime> HasErrorType for OfaRuntimeWrapper<Runtime> {
    type Error = Runtime::Error;
}
