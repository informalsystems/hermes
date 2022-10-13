use crate::base::all_for_one::chain::{AfoBaseChain, AfoCounterpartyChain};
use crate::full::telemetry::traits::telemetry::HasTelemetry;

pub trait AfoFullChain<Counterparty>: AfoBaseChain<Counterparty> + HasTelemetry
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoFullChain<Counterparty> for Chain
where
    Chain: AfoBaseChain<Counterparty> + HasTelemetry,
    Counterparty: AfoCounterpartyChain<Self>,
{
}
