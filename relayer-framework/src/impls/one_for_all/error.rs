use crate::traits::one_for_all::chain::OfaChain;

pub struct OfaError<Chain: OfaChain> {
    pub error: Chain::Error,
}

impl<Chain: OfaChain> OfaError<Chain> {
    pub fn new(error: Chain::Error) -> Self {
        Self { error }
    }
}
