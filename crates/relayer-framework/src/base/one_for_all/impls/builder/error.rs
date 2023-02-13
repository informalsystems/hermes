use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::builder::OfaBuilder;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;

impl<Builder> HasErrorType for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    type Error = Builder::Error;
}
