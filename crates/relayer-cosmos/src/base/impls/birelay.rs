use ibc_relayer_framework::base::one_for_all::traits::birelay::{
    OfaBiRelay, OfaBiRelayPreset, OfaBiRelayTypes,
};
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

use crate::base::error::{BaseError, Error};
use crate::base::traits::birelay::CosmosBiRelay;
use crate::base::types::birelay::CosmosBiRelayWrapper;
use crate::base::types::relay::CosmosRelayWrapper;

impl<BiRelay> OfaBiRelayTypes for CosmosBiRelayWrapper<BiRelay>
where
    BiRelay: CosmosBiRelay,
    BiRelay::Preset: OfaBiRelayPreset<Self>,
{
    type Preset = BiRelay::Preset;

    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type RelayAToB = CosmosRelayWrapper<BiRelay::RelayAToB>;

    type RelayBToA = CosmosRelayWrapper<BiRelay::RelayBToA>;
}

impl<BiRelay> OfaBiRelay for CosmosBiRelayWrapper<BiRelay>
where
    BiRelay: CosmosBiRelay,
    BiRelay::Preset: OfaBiRelayPreset<Self>,
{
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime> {
        self.birelay.runtime()
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }

    fn relay_a_to_b(&self) -> &OfaRelayWrapper<Self::RelayAToB> {
        self.birelay.relay_a_to_b()
    }

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<Self::RelayBToA> {
        self.birelay.relay_b_to_a()
    }

    fn error_a_to_b(e: Error) -> Error {
        e
    }

    fn error_b_to_a(e: Error) -> Error {
        e
    }
}
