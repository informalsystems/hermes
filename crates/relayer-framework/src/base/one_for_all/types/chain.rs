use crate::base::chain::traits::queries::write_acknowledgement::CanQueryWriteAck;

#[derive(Clone)]
pub struct OfaChainWrapper<Chain> {
    pub chain: Chain,
}

impl<Chain> OfaChainWrapper<Chain> {
    pub fn new(chain: Chain) -> Self {
        Self { chain }
    }
}

impl<Chain, Counterparty> CanQueryWriteAck<Counterparty> for OfaChainWrapper<Chain> {}
