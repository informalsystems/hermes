use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_all_in_one::one_for_all::traits::birelay::OfaBiRelay;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;

use crate::contexts::birelay::CosmosBiRelay;
use crate::contexts::relay::CosmosRelay;
use crate::types::error::{BaseError, Error};

impl<ChainA, ChainB> OfaBiRelay for CosmosBiRelay<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type RelayAToB = CosmosRelay<ChainA, ChainB>;

    type RelayBToA = CosmosRelay<ChainB, ChainA>;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }

    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }

    fn relay_a_to_b(&self) -> &OfaRelayWrapper<Self::RelayAToB> {
        &self.relay_a_to_b
    }

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<Self::RelayBToA> {
        &self.relay_b_to_a
    }

    fn relay_error(e: Error) -> Error {
        e
    }
}
