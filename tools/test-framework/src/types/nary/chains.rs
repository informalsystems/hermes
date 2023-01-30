/*!
   Constructs for N-ary connected chains.
*/

use core::convert::{From, TryFrom};
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::error::Error;
use crate::types::binary::chains::ConnectedChains as BinaryConnectedChains;
use crate::types::env::{prefix_writer, EnvWriter, ExportEnv};
use crate::types::nary::aliases::*;
use crate::types::nary::foreign_client::*;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::util::array::try_into_array;

/**
   A fixed-size N-ary connected chains as specified by `SIZE`.

   Contains `SIZE` number of [`ChainHandle`]s, `SIZE` number of
   [`FullNode`]s, and `SIZE`x`SIZE` numbers of [`ForeignClient`] pairs.

   A `ConnectedChains` can be constructed by first constructing
   a [`DynamicConnectedChains`], and then calling
   [`try_into()`](core::convert::TryInto::try_into).
*/
#[derive(Clone)]
pub struct NaryConnectedChains<Handle: ChainHandle, const SIZE: usize> {
    chain_handles: [Handle; SIZE],
    full_nodes: [FullNode; SIZE],
    foreign_clients: ForeignClientPairs<Handle, SIZE>,
}

/**
   A dynamic-sized N-ary connected chains, based on the
   length of the underlying [`Vec`]. Each list must have the
   same length.

   The main use of [`DynamicConnectedChains`] is to convert it into
   a [`NaryConnectedChains`].
*/
#[derive(Clone)]
pub struct DynamicConnectedChains<Handle: ChainHandle> {
    chain_handles: Vec<Handle>,
    full_nodes: Vec<FullNode>,
    pub foreign_clients: Vec<Vec<ForeignClient<Handle, Handle>>>,
}

/**
   A pair of binary [`ConnectedChains`](BinaryConnectedChains) that are
   tagged by a `Handle: CHainHandle` and the const generics
   `CHAIN_A: usize` and `CHAIN_B: usize`.

   Recall that binary [`ConnectedChains`](BinaryConnectedChains) is tagged
   by two generic types `ChainA: ChainHandle` and `ChainB: ChainHandle`.
   For the case of N-ary chains, all elements must have the same type
   `Handle: ChainHandle`. But we want to still able to differentiate
   them when used as type parameter to `ConnectedChains`.

   The solution is to tag each `Handle` with the const generic
   positions. So the first chain is `MonoTagged<Size<CHAIN_A>, Handle>`,
   which has a different type from the second chain
   `MonoTagged<Size<CHAIN_B>, Handle>`.

   Since writing the fully qualified chain types are rather cumbersome,
   we use the type alias `TaggedConnectedChains` to refer to
   connected chains that are parameterized by const generics rather
   than the usual abstract type tags.
*/
pub type NthConnectedChains<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    BinaryConnectedChains<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>>;

/**
   A [`FullNode`] that is tagged by a `Handle: ChainHandle` and
   the const generics `TAG: usize`.
*/
pub type NthFullNode<const TAG: usize, Handle> = MonoTagged<NthChainHandle<TAG, Handle>, FullNode>;

impl<Handle: ChainHandle, const SIZE: usize> NaryConnectedChains<Handle, SIZE> {
    /**
       Get a connected chain pair at position `CHAIN_A` and `CHAIN_B`, which
       must be less than `SIZE`.

       Returns a binary [`ConnectedChains`](BinaryConnectedChains) with the
       first chain tagged by `CHAIN_A`, and second chain tagged by `CHAIN_B`.
    */
    pub fn connected_chains_at<const CHAIN_A: usize, const CHAIN_B: usize>(
        &self,
    ) -> Result<NthConnectedChains<CHAIN_A, CHAIN_B, Handle>, Error> {
        if CHAIN_A >= SIZE || CHAIN_B >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get chains beyond position {}/{}",
                CHAIN_A,
                CHAIN_B
            )))
        } else {
            let node_a = self.full_nodes[CHAIN_A].clone();
            let node_b = self.full_nodes[CHAIN_B].clone();

            let handle_a = self.chain_handles[CHAIN_A].clone();
            let handle_b = self.chain_handles[CHAIN_B].clone();

            let foreign_clients = self.foreign_client_pair_at::<CHAIN_A, CHAIN_B>()?;

            Ok(BinaryConnectedChains::new(
                MonoTagged::new(handle_a),
                MonoTagged::new(handle_b),
                MonoTagged::new(node_a),
                MonoTagged::new(node_b),
                foreign_clients,
            ))
        }
    }

    /**
       Get the [`FullNode`] at position `POS`, which must be less than `SIZE`.

       Returns a [`FullNode`] tagged with `POS`.
    */
    pub fn full_node_at<const POS: usize>(&self) -> Result<NthFullNode<POS, Handle>, Error> {
        if POS >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get full_node beyond position {}",
                POS
            )))
        } else {
            let full_node: FullNode = self.full_nodes[POS].clone();
            Ok(MonoTagged::new(full_node))
        }
    }

    /**
       Get the [`ChainHandle`] at position `POS`, which must be less than `SIZE`.

       Returns a [`ChainHandle`] tagged by `POS`.
    */
    pub fn chain_handle_at<const POS: usize>(&self) -> Result<NthChainHandle<POS, Handle>, Error> {
        if POS >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get full_node beyond position {}",
                POS
            )))
        } else {
            let handle = self.chain_handles[POS].clone();
            Ok(MonoTagged::new(handle))
        }
    }

    /**
       Get the [`ForeignClient`] with the source chain at position
       `SRC: usize` and destination chain at position `DEST: usize`,
       which must be less than `SIZE`.
    */
    pub fn foreign_client_at<const SRC: usize, const DEST: usize>(
        &self,
    ) -> Result<NthForeignClient<Handle, DEST, SRC>, Error> {
        self.foreign_clients.foreign_client_at::<SRC, DEST>()
    }

    pub fn foreign_client_pair_at<const CHAIN_A: usize, const CHAIN_B: usize>(
        &self,
    ) -> Result<NthForeignClientPair<Handle, CHAIN_A, CHAIN_B>, Error> {
        self.foreign_clients
            .foreign_client_pair_at::<CHAIN_A, CHAIN_B>()
    }

    pub fn chain_handles(&self) -> &[Handle; SIZE] {
        &self.chain_handles
    }

    pub fn full_nodes(&self) -> &[FullNode; SIZE] {
        &self.full_nodes
    }

    pub fn foreign_clients(&self) -> &ForeignClientPairs<Handle, SIZE> {
        &self.foreign_clients
    }
}

impl<Handle: ChainHandle> DynamicConnectedChains<Handle> {
    pub fn new(
        chain_handles: Vec<Handle>,
        full_nodes: Vec<FullNode>,
        foreign_clients: Vec<Vec<ForeignClient<Handle, Handle>>>,
    ) -> Self {
        Self {
            chain_handles,
            full_nodes,
            foreign_clients,
        }
    }

    pub fn chain_handles(&self) -> &Vec<Handle> {
        &self.chain_handles
    }

    pub fn full_nodes(&self) -> &Vec<FullNode> {
        &self.full_nodes
    }

    pub fn foreign_clients(&self) -> &Vec<Vec<ForeignClient<Handle, Handle>>> {
        &self.foreign_clients
    }
}

impl<Handle: ChainHandle, const SIZE: usize> From<NaryConnectedChains<Handle, SIZE>>
    for DynamicConnectedChains<Handle>
{
    fn from(chains: NaryConnectedChains<Handle, SIZE>) -> Self {
        Self {
            chain_handles: chains.chain_handles.into(),
            full_nodes: chains.full_nodes.into(),
            foreign_clients: chains.foreign_clients.into_nested_vec(),
        }
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedChains<Handle>>
    for NaryConnectedChains<Handle, SIZE>
{
    type Error = Error;

    fn try_from(chains: DynamicConnectedChains<Handle>) -> Result<Self, Error> {
        Ok(NaryConnectedChains {
            chain_handles: try_into_array(chains.chain_handles)?,
            full_nodes: try_into_array(chains.full_nodes)?,
            foreign_clients: chains.foreign_clients.try_into()?,
        })
    }
}

impl<Handle: ChainHandle> From<NaryConnectedChains<Handle, 2>>
    for NthConnectedChains<0, 1, Handle>
{
    fn from(chains: NaryConnectedChains<Handle, 2>) -> Self {
        chains.connected_chains_at::<0, 1>().unwrap()
    }
}

impl<Handle: ChainHandle, const SIZE: usize> ExportEnv for NaryConnectedChains<Handle, SIZE> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        for (i, node) in self.full_nodes.iter().enumerate() {
            writer.write_env(
                &format!("CHAIN_ID_{i}"),
                &format!("{}", node.chain_driver.chain_id),
            );

            self.foreign_clients.export_env(writer);

            node.export_env(&mut prefix_writer(&format!("NODE_{i}"), writer));
        }
    }
}
