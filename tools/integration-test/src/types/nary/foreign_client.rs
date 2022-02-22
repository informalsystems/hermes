use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use super::aliases::NthHandle;
use crate::error::Error;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::tagged::*;
use crate::util::array::{into_nested_vec, try_into_nested_array};

/**
   A [`ForeignClient`] that is tagged by a `Handle: ChainHandle` and
   the const generics `DEST: usize` and `SRC: usize`.
*/
pub type NthForeignClient<Handle, const DST: usize, const SRC: usize> =
    ForeignClient<NthHandle<Handle, DST>, NthHandle<Handle, SRC>>;

pub type NthForeignClientPair<Handle, const DST: usize, const SRC: usize> =
    ForeignClientPair<NthHandle<Handle, DST>, NthHandle<Handle, SRC>>;

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

    pub fn foreign_client_pair_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<NthForeignClientPair<Handle, FIRST, SECOND>, Error> {
        let client_a_to_b = self.foreign_client_at::<FIRST, SECOND>()?;
        let client_b_to_a = self.foreign_client_at::<SECOND, FIRST>()?;

        Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
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
