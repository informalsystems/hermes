use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::one_for_all::traits::builder::OfaFullBuilder;
use crate::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder> HasErrorType for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
{
    type Error = Builder::Error;
}
