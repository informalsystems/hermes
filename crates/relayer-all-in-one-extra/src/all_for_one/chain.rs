use ibc_relayer_all_in_one::all_for_one::chain::{AfoBaseChain, AfoCounterpartyChain};
use ibc_relayer_components_extra::telemetry::traits::telemetry::HasTelemetry;

use crate::all_for_one::runtime::HasAfoFullRuntime;

pub trait AfoFullChain<Counterparty>:
    AfoBaseChain<Counterparty> + HasAfoFullRuntime<AfoFullRuntime = Self::AfoBaseRuntime> + HasTelemetry
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoFullChain<Counterparty> for Chain
where
    Chain: AfoBaseChain<Counterparty>
        + HasAfoFullRuntime<AfoFullRuntime = Self::AfoBaseRuntime>
        + HasTelemetry,
    Counterparty: AfoCounterpartyChain<Self>,
{
}
