use crate::base::all_for_one::traits::chain::{AfoChainContext, AfoCounterpartyContext};
use crate::full::telemetry::traits::telemetry::HasTelemetry;

pub trait AfoFullChainContext<Counterparty>: AfoChainContext<Counterparty> + HasTelemetry
where
    Counterparty: AfoCounterpartyContext<Self>,
{
}

impl<Chain, Counterparty> AfoFullChainContext<Counterparty> for Chain
where
    Chain: AfoChainContext<Counterparty> + HasTelemetry,
    Counterparty: AfoCounterpartyContext<Self>,
{
}
