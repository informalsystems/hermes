use ibc_relayer_all_in_one::base::all_for_one::chain::AfoCounterpartyChain;
use ibc_relayer_all_in_one::extra::all_for_one::chain::AfoFullChain;

use crate::base::all_for_one::chain::AfoCosmosBaseChain;

pub trait AfoCosmosFullChain<Counterparty>:
    AfoCosmosBaseChain<Counterparty> + AfoFullChain<Counterparty>
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

impl<Chain, Counterparty> AfoCosmosFullChain<Counterparty> for Chain
where
    Chain: AfoCosmosBaseChain<Counterparty> + AfoFullChain<Counterparty>,
    Counterparty: AfoCounterpartyChain<Self>,
{
}
