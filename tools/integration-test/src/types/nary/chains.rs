use core::convert::{From, TryFrom};
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::error::Error;
use crate::types::binary::chains::ConnectedChains as BinaryConnectedChains;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::util::array::{into_nested_vec, try_into_array, try_into_nested_array};

#[derive(Clone)]
pub struct ConnectedChains<Handle: ChainHandle, const SIZE: usize> {
    pub chain_handles: [Handle; SIZE],
    pub full_nodes: [FullNode; SIZE],
    pub foreign_clients: [[ForeignClient<Handle, Handle>; SIZE]; SIZE],
}

#[derive(Clone)]
pub struct DynamicConnectedChains<Handle: ChainHandle> {
    pub chain_handles: Vec<Handle>,
    pub full_nodes: Vec<FullNode>,
    pub foreign_clients: Vec<Vec<ForeignClient<Handle, Handle>>>,
}

pub struct Size<const TAG: usize>;

pub type TaggedConnectedChains<Handle, const FIRST: usize, const SECOND: usize> =
    BinaryConnectedChains<MonoTagged<Size<FIRST>, Handle>, MonoTagged<Size<SECOND>, Handle>>;

pub type TaggedHandle<Handle, const TAG: usize> = MonoTagged<Size<TAG>, Handle>;

pub type TaggedFullNode<Handle, const TAG: usize> = MonoTagged<TaggedHandle<Handle, TAG>, FullNode>;

pub type TaggedForeignClient<Handle, const FIRST: usize, const SECOND: usize> =
    ForeignClient<MonoTagged<Size<FIRST>, Handle>, MonoTagged<Size<SECOND>, Handle>>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedChains<Handle, SIZE> {
    pub fn connected_chains_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedConnectedChains<Handle, FIRST, SECOND>, Error> {
        if FIRST >= SIZE || SECOND >= SIZE {
            Err(eyre!(
                "cannot get chains beyond position {}/{}",
                FIRST,
                SECOND
            ))
        } else {
            let node_a = self.full_nodes[FIRST].clone();
            let node_b = self.full_nodes[SECOND].clone();

            let handle_a = self.chain_handles[FIRST].clone();
            let handle_b = self.chain_handles[SECOND].clone();

            let client_a_to_b = self.foreign_clients[FIRST][SECOND].clone();
            let client_b_to_a = self.foreign_clients[SECOND][FIRST].clone();

            Ok(BinaryConnectedChains {
                node_a: MonoTagged::new(node_a),
                node_b: MonoTagged::new(node_b),
                handle_a: MonoTagged::new(handle_a),
                handle_b: MonoTagged::new(handle_b),
                client_a_to_b: client_a_to_b.map_chain(MonoTagged::new, MonoTagged::new),
                client_b_to_a: client_b_to_a.map_chain(MonoTagged::new, MonoTagged::new),
            })
        }
    }

    pub fn full_node_at<const POS: usize>(&self) -> Result<TaggedFullNode<Handle, POS>, Error> {
        if POS >= SIZE {
            Err(eyre!("cannot get full_node beyond position {}", POS))
        } else {
            let full_node: FullNode = self.full_nodes[POS].clone();
            Ok(MonoTagged::new(full_node))
        }
    }

    pub fn chain_handle_at<const POS: usize>(&self) -> Result<TaggedHandle<Handle, POS>, Error> {
        if POS >= SIZE {
            Err(eyre!("cannot get full_node beyond position {}", POS))
        } else {
            let handle = self.chain_handles[POS].clone();
            Ok(MonoTagged::new(handle))
        }
    }

    pub fn foreign_client_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedForeignClient<Handle, SECOND, FIRST>, Error> {
        if FIRST >= SIZE || SECOND >= SIZE {
            Err(eyre!(
                "cannot get foreign client beyond position {}/{}",
                FIRST,
                SECOND
            ))
        } else {
            let client = self.foreign_clients[FIRST][SECOND]
                .clone()
                .map_chain(MonoTagged::new, MonoTagged::new);

            Ok(client)
        }
    }
}

impl<Handle: ChainHandle, const SIZE: usize> From<ConnectedChains<Handle, SIZE>>
    for DynamicConnectedChains<Handle>
{
    fn from(chains: ConnectedChains<Handle, SIZE>) -> Self {
        Self {
            chain_handles: chains.chain_handles.into(),
            full_nodes: chains.full_nodes.into(),
            foreign_clients: into_nested_vec(chains.foreign_clients),
        }
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedChains<Handle>>
    for ConnectedChains<Handle, SIZE>
{
    type Error = Error;

    fn try_from(chains: DynamicConnectedChains<Handle>) -> Result<Self, Error> {
        Ok(ConnectedChains {
            chain_handles: try_into_array(chains.chain_handles)?,
            full_nodes: try_into_array(chains.full_nodes)?,
            foreign_clients: try_into_nested_array(chains.foreign_clients)?,
        })
    }
}

impl<Handle: ChainHandle> From<ConnectedChains<Handle, 2>> for TaggedConnectedChains<Handle, 0, 1> {
    fn from(chains: ConnectedChains<Handle, 2>) -> Self {
        chains.connected_chains_at::<0, 1>().unwrap()
    }
}
