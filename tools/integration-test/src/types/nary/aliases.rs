use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::error::Error;
use crate::types::tagged::*;
use crate::util::array::{into_nested_vec, try_into_nested_array};

/**
   Lifts a const generic `usize` into a type.

   This allows us to use `usize` as a tag, for example,
   `MonoTagged<Size<1>, String>` is a `String` that is
   tagged by the const generic `1`.
*/
pub enum Size<const TAG: usize> {}

/**
   Tag a `Handle: ChainHandle` type with a const generic `TAG: usize`.

   In an N-ary chain implementation, we have to use the same
   `Handle: ChainHandle` type for all elements in the N-ary data
   structures. However since the [`ChainHandle`] type is also being
   used to tag other values, we want to be able to differentiate
   between tagged values coming from chains at different positions
   in the N-ary setup.

   The solution is to tag each `Handle` with the const generic
   positions. With that a position-tagged type like
   `MonoTagged<Size<0>, Handle>` would have a different type
   from the type tagged at a different position like
   `MonoTagged<Size<1>, Handle>`.

   To reduce the boilerplate, we define the type alias
   `TaggedHandle` so that less typing is needed to refer
   to `ChainHandle`s that are tagged by position.

*/
pub type NthHandle<Handle, const POS: usize> = MonoTagged<Size<POS>, Handle>;

/**
   A [`ForeignClient`] that is tagged by a `Handle: ChainHandle` and
   the const generics `DEST: usize` and `SRC: usize`.
*/
pub type NthForeignClient<Handle, const DST: usize, const SRC: usize> =
    ForeignClient<NthHandle<Handle, DST>, NthHandle<Handle, SRC>>;

#[derive(Clone)]
pub struct ForeignClientPairs<Handle: ChainHandle, const SIZE: usize> {
    foreign_clients: [[ForeignClient<Handle, Handle>; SIZE]; SIZE],
}

impl<Handle: ChainHandle, const SIZE: usize> ForeignClientPairs<Handle, SIZE> {
    /**
       Get the [`ForeignClient`] with the source chain at position
       `SRC: usize` and destination chain at position `DEST: usize`,
       which must be less than `SIZE`.
    */
    pub fn foreign_client_at<const SRC: usize, const DEST: usize>(
        &self,
    ) -> Result<NthForeignClient<Handle, DEST, SRC>, Error> {
        if SRC >= SIZE || DEST >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get foreign client beyond position {}/{}",
                SRC,
                DEST
            )))
        } else {
            let client = self.foreign_clients[SRC][DEST]
                .clone()
                .map_chain(MonoTagged::new, MonoTagged::new);

            Ok(client)
        }
    }

    pub fn into_nested_vec(self) -> Vec<Vec<ForeignClient<Handle, Handle>>> {
        into_nested_vec(self.foreign_clients)
    }

    pub fn try_from_nested_vec(
        foreign_clients: Vec<Vec<ForeignClient<Handle, Handle>>>,
    ) -> Result<Self, Error> {
        let foreign_clients = try_into_nested_array(foreign_clients)?;

        Ok(Self { foreign_clients })
    }
}
