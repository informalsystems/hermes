use ibc_relayer_framework::base::all_for_one::chain::AfoCounterpartyContext;
use ibc_relayer_framework::full::all_for_one::chain::AfoFullChainContext;

use crate::cosmos::base::all_for_one::chain::AfoCosmosChainContext;

pub trait AfoCosmosFullChainContext<Counterparty>:
    AfoCosmosChainContext<Counterparty> + AfoFullChainContext<Counterparty>
where
    Counterparty: AfoCounterpartyContext<Self>,
{
}

impl<Chain, Counterparty> AfoCosmosFullChainContext<Counterparty> for Chain
where
    Chain: AfoCosmosChainContext<Counterparty> + AfoFullChainContext<Counterparty>,
    Counterparty: AfoCounterpartyContext<Self>,
{
}
