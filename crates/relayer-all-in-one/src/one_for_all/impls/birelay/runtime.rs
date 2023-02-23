use crate::base::core::traits::error::HasErrorType;
use crate::one_for_all::traits::birelay::OfaBiRelay;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::runtime::HasRuntime;

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
