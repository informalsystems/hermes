use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<Runtime: OfaBaseRuntime> HasErrorType for OfaRuntimeWrapper<Runtime> {
    type Error = Runtime::Error;
}
