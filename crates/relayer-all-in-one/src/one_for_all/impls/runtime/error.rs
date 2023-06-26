use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<Runtime> HasErrorType for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    type Error = Runtime::Error;
}
