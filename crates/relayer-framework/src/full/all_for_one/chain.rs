use crate::base::all_for_one::chain::{AfoBaseChain, AfoCounterpartyChain};
use crate::full::all_for_one::runtime::HasAfoFullRuntime;
use crate::full::telemetry::traits::telemetry::HasTelemetry;

pub trait AfoFullChain<Counterparty>:
    AfoBaseChain<Counterparty> + HasAfoFullRuntime + HasTelemetry
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoFullChain<Counterparty> for Chain
where
    Chain: AfoBaseChain<Counterparty> + HasAfoFullRuntime + HasTelemetry,
    Counterparty: AfoCounterpartyChain<Self>,
{
}
