use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::path::PathBuf;

use crate::error::Error;
use crate::types::binary::chains::DropChainHandle;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;

pub struct ConnectedChains<Handle: ChainHandle, const SIZE: usize> {
    pub config_path: PathBuf,
    pub registry: SharedRegistry<Handle>,
    pub chain_handles: [DropChainHandle<Handle>; SIZE],
    pub full_nodes: [FullNode; SIZE],
    pub foreign_clients: [[ForeignClient<Handle, Handle>; SIZE]; SIZE],
}

pub struct Size<const TAG: usize>;

pub type TaggedHandle<Handle, const TAG: usize> = MonoTagged<Size<TAG>, Handle>;

pub type TaggedFullNode<'a, Handle, const TAG: usize> =
    MonoTagged<TaggedHandle<Handle, TAG>, &'a FullNode>;

pub type TaggedForeignClient<Handle, const FIRST: usize, const SECOND: usize> =
    ForeignClient<MonoTagged<Size<FIRST>, Handle>, MonoTagged<Size<SECOND>, Handle>>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedChains<Handle, SIZE> {
    pub fn full_node_at<const POS: usize>(&self) -> Result<TaggedFullNode<Handle, POS>, Error> {
        let full_node = self.raw_full_node_at(POS)?;
        Ok(MonoTagged::new(full_node))
    }

    pub fn chain_handle_at<const POS: usize>(&self) -> Result<TaggedHandle<Handle, POS>, Error> {
        let handle = self.raw_chain_handle_at(POS)?;
        Ok(MonoTagged::new(handle.clone()))
    }

    pub fn foreign_client_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedForeignClient<Handle, SECOND, FIRST>, Error> {
        let client = self.raw_foreign_client_at(FIRST, SECOND)?;

        Ok(ForeignClient::restore(
            client.id.clone(),
            MonoTagged::new(client.dst_chain.clone()),
            MonoTagged::new(client.src_chain.clone()),
        ))
    }

    pub fn raw_full_node_at(&self, pos: usize) -> Result<&FullNode, Error> {
        if pos >= SIZE {
            Err(eyre!("cannot get full_node beyond position {}", pos))
        } else {
            self.full_nodes
                .get(pos)
                .ok_or_else(|| eyre!("failed to get chain handle at position {}", pos))
        }
    }

    pub fn raw_chain_handle_at(&self, pos: usize) -> Result<&Handle, Error> {
        if pos >= SIZE {
            Err(eyre!("cannot get chain handle beyond position {}", pos))
        } else {
            self.chain_handles
                .get(pos)
                .map(|handle| &handle.0)
                .ok_or_else(|| eyre!("failed to get chain handle at position {}", pos))
        }
    }

    pub fn raw_foreign_client_at(
        &self,
        pos_a: usize,
        pos_b: usize,
    ) -> Result<&ForeignClient<Handle, Handle>, Error> {
        if pos_a >= SIZE {
            Err(eyre!("cannot get chain handle beyond position {}", pos_a))
        } else if pos_b >= SIZE {
            Err(eyre!("cannot get chain handle beyond position {}", pos_b))
        } else {
            self.foreign_clients
                .get(pos_a)
                .and_then(|slice| slice.get(pos_b))
                .ok_or_else(|| {
                    eyre!(
                        "failed to get foreign client at position {}, {}",
                        pos_a,
                        pos_b
                    )
                })
        }
    }
}
