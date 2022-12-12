use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeWrapper};

impl<Runtime: OfaRuntime> HasErrorType for OfaRuntimeWrapper<Runtime> {
    type Error = Runtime::Error;
}
