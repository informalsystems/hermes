use core::convert::{From, TryFrom};
use eyre::eyre;
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::SharedConfig;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::path::PathBuf;

use crate::error::Error;
use crate::types::binary::chains::ConnectedChains as BinaryConnectedChains;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::util::array::{try_into_array, try_into_nested_array};

#[derive(Clone)]
pub struct ConnectedChains<Handle: ChainHandle, const SIZE: usize> {
    pub config_path: PathBuf,
    pub config: SharedConfig,
    pub registry: SharedRegistry<ProdChainHandle>,
    pub chain_handles: [Handle; SIZE],
    pub full_nodes: [FullNode; SIZE],
    pub foreign_clients: [[ForeignClient<Handle, Handle>; SIZE]; SIZE],
}

#[derive(Clone)]
pub struct DynamicConnectedChains<Handle: ChainHandle> {
    pub config_path: PathBuf,
    pub config: SharedConfig,
    pub registry: SharedRegistry<ProdChainHandle>,
    pub chain_handles: Vec<Handle>,
    pub full_nodes: Vec<FullNode>,
    pub foreign_clients: Vec<Vec<ForeignClient<Handle, Handle>>>,
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

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedChains<Handle>>
    for ConnectedChains<Handle, SIZE>
{
    type Error = Error;

    fn try_from(chains: DynamicConnectedChains<Handle>) -> Result<Self, Error> {
        Ok(ConnectedChains {
            config_path: chains.config_path,
            config: chains.config,
            registry: chains.registry,
            chain_handles: try_into_array(chains.chain_handles)?,
            full_nodes: try_into_array(chains.full_nodes)?,
            foreign_clients: try_into_nested_array(chains.foreign_clients)?,
        })
    }
}

impl<Handle: ChainHandle> From<ConnectedChains<Handle, 2>>
    for BinaryConnectedChains<Handle, Handle>
{
    fn from(chains: ConnectedChains<Handle, 2>) -> Self {
        let [handle_a, handle_b] = chains.chain_handles;
        let [node_a, node_b] = chains.full_nodes;
        let [[_, client_a_to_b], [client_b_to_a, _]] = chains.foreign_clients;

        BinaryConnectedChains {
            config_path: chains.config_path,
            config: chains.config,
            registry: chains.registry,
            handle_a,
            handle_b,
            node_a: MonoTagged::new(node_a),
            node_b: MonoTagged::new(node_b),
            client_a_to_b,
            client_b_to_a,
        }
    }
}
