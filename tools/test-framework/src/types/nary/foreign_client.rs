use std::collections::HashMap;

use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use super::aliases::NthChainHandle;
use crate::error::Error;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::tagged::*;

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
    foreign_clients: HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>>,
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
        let src_clients = self
            .foreign_clients
            .get(&SRC)
            .ok_or_else(|| Error::generic(eyre!("No client entries found for chain `{SRC}`")))?;
        let client = src_clients
            .get(&DEST)
            .ok_or_else(|| {
                Error::generic(eyre!("No client entry found for chain `{SRC}` to `{DEST}`"))
            })?
            .clone()
            .map_chain(MonoTagged::new, MonoTagged::new);
        Ok(client)
    }

    pub fn foreign_client_pair_at<const CHAIN_A: usize, const CHAIN_B: usize>(
        &self,
    ) -> Result<NthForeignClientPair<Handle, CHAIN_A, CHAIN_B>, Error> {
        let client_a_to_b = self.foreign_client_at::<CHAIN_A, CHAIN_B>()?;
        let client_b_to_a = self.foreign_client_at::<CHAIN_B, CHAIN_A>()?;

        Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
    }

    pub fn into_nested_vec(self) -> HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>> {
        self.foreign_clients
    }
}

impl<Handle: ChainHandle, const SIZE: usize>
    TryFrom<HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>>>
    for ForeignClientPairs<Handle, SIZE>
{
    type Error = Error;

    fn try_from(
        clients: HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>>,
    ) -> Result<Self, Error> {
        let foreign_clients = clients;
        Ok(Self { foreign_clients })
    }
}

impl<Handle: ChainHandle, const SIZE: usize> ExportEnv for ForeignClientPairs<Handle, SIZE> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        for inner_clients in self.foreign_clients.iter() {
            for client in inner_clients.1.iter() {
                writer.write_env(
                    &format!("CLIENT_ID_{}_to_{}", inner_clients.0, client.0),
                    &format!("{}", client.1.id()),
                );
            }
        }
    }
}
