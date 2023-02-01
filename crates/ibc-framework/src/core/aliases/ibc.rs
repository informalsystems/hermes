use crate::core::traits::host::HasHostTypes;
use crate::core::traits::ibc::HasIbcTypes;

pub type Height<Context> = <Context as HasHostTypes>::Height;

pub type Timestamp<Context> = <Context as HasHostTypes>::Timestamp;

pub type ClientId<Context> = <Context as HasIbcTypes>::ClientId;
