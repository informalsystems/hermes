use dyn_clone::DynClone;

use crate::dynamic_typing::AsAny;
use crate::prelude::*;

use crate::core::ics24_host::identifier::ClientId;
use crate::Height;

pub trait Misbehaviour:
    AsAny + sealed::ErasedPartialEqMisbehaviour + DynClone + core::fmt::Debug + Send + Sync
{
    /// The type of client (eg. Tendermint)
    fn client_id(&self) -> &ClientId;

    /// The height of the consensus state
    fn height(&self) -> Height;
}

// Implements `Clone` for `Box<dyn Misbehaviour>`
dyn_clone::clone_trait_object!(Misbehaviour);

impl PartialEq for dyn Misbehaviour {
    fn eq(&self, other: &Self) -> bool {
        self.eq_misbehaviour(other)
    }
}
mod sealed {
    use super::*;

    pub trait ErasedPartialEqMisbehaviour {
        fn eq_misbehaviour(&self, other: &dyn Misbehaviour) -> bool;
    }

    impl<H> ErasedPartialEqMisbehaviour for H
    where
        H: Misbehaviour + PartialEq,
    {
        fn eq_misbehaviour(&self, other: &dyn Misbehaviour) -> bool {
            other
                .as_any()
                .downcast_ref::<H>()
                .map_or(false, |h| self == h)
        }
    }
}
