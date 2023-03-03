use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;
use crate::transaction::traits::types::HasTxTypes;

pub trait CanLogNonce: HasTxTypes + HasLoggerType {
    fn log_nonce<'a>(nonce: &'a Self::Nonce) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}
