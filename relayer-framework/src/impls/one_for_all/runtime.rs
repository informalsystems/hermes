use crate::impls::one_for_all::error::OfaError;
use crate::traits::core::ErrorContext;
use crate::traits::one_for_all::chain::OfaChain;

pub struct OfaRuntimeContext<Chain: OfaChain> {
    pub runtime: Chain::Runtime,
}

impl<Chain: OfaChain> ErrorContext for OfaRuntimeContext<Chain> {
    type Error = OfaError<Chain>;
}
