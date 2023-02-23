use crate::base::core::traits::error::HasErrorType;
use crate::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<Runtime: OfaBaseRuntime> HasErrorType for OfaRuntimeWrapper<Runtime> {
    type Error = Runtime::Error;
}
