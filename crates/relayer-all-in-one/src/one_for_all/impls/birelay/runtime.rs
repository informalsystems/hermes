use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::base::one_for_all::traits::birelay::OfaBiRelay;
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<BiRelay> HasRuntime for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: OfaBiRelay,
{
    type Runtime = OfaRuntimeWrapper<BiRelay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.birelay.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> BiRelay::Error {
        BiRelay::runtime_error(e)
    }
}
