use crate::base::core::traits::error::HasErrorType;
use crate::full::one_for_all::traits::builder::OfaFullBuilder;
use crate::full::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder> HasErrorType for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
{
    type Error = Builder::Error;
}
