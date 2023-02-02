use core::convert::TryFrom;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use super::aliases::NthChainHandle;
use crate::error::Error;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::tagged::*;
use crate::util::array::{into_nested_vec, try_into_nested_array};

/**
   A [`ForeignClient`] that is tagged by a `Handle: ChainHandle` and
   the const generics `DEST: usize` and `SRC: usize`.
*/
pub type NthForeignClient<Handle, const DST: usize, const SRC: usize> =
    ForeignClient<NthChainHandle<DST, Handle>, NthChainHandle<SRC, Handle>>;

pub type NthForeignClientPair<Handle, const DST: usize, const SRC: usize> =
    ForeignClientPair<NthChainHandle<DST, Handle>, NthChainHandle<SRC, Handle>>;

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

    pub fn foreign_client_pair_at<const CHAIN_A: usize, const CHAIN_B: usize>(
        &self,
    ) -> Result<NthForeignClientPair<Handle, CHAIN_A, CHAIN_B>, Error> {
        let client_a_to_b = self.foreign_client_at::<CHAIN_A, CHAIN_B>()?;
        let client_b_to_a = self.foreign_client_at::<CHAIN_B, CHAIN_A>()?;

        Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
    }

    pub fn into_nested_vec(self) -> Vec<Vec<ForeignClient<Handle, Handle>>> {
        into_nested_vec(self.foreign_clients)
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<Vec<Vec<ForeignClient<Handle, Handle>>>>
    for ForeignClientPairs<Handle, SIZE>
{
    type Error = Error;

    fn try_from(clients: Vec<Vec<ForeignClient<Handle, Handle>>>) -> Result<Self, Error> {
        let foreign_clients = try_into_nested_array(clients)?;
        Ok(Self { foreign_clients })
    }
}

impl<Handle: ChainHandle, const SIZE: usize> ExportEnv for ForeignClientPairs<Handle, SIZE> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        for (source, inner_clients) in self.foreign_clients.iter().enumerate() {
            for (destination, client) in inner_clients.iter().enumerate() {
                writer.write_env(
                    &format!("CLIENT_ID_{source}_to_{destination}"),
                    &format!("{}", client.id()),
                );
            }
        }
    }
}
