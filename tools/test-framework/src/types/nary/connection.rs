/*!
   Constructs for N-ary connected connections.
*/

use core::convert::TryFrom;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;

use super::aliases::NthChainHandle;
use crate::error::Error;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::tagged::*;
use crate::util::array::{into_nested_vec, try_into_nested_array};

/**
   A fixed-size N-ary connected connections as specified by `SIZE`.

   Contains `SIZE`x`SIZE` number of binary [`ConnectedConnection`]s.
*/
#[derive(Debug, Clone)]
pub struct ConnectedConnections<Handle: ChainHandle, const SIZE: usize> {
    connections: [[ConnectedConnection<Handle, Handle>; SIZE]; SIZE],
}

/**
   A dynamic-sized N-ary connected connections, made of a
   nested vector of binary [`ConnectedConnection`] which must be
   in the same dimension.
*/
#[derive(Debug, Clone)]
pub struct DynamicConnectedConnections<Handle: ChainHandle> {
    connections: Vec<Vec<ConnectedConnection<Handle, Handle>>>,
}

/**
   A tagged binary [`ConnectedConnection`] that is connected between the chains at
   position `CHAIN_A` and `CHAIN_B`.
*/
pub type NthConnectedConnection<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    ConnectedConnection<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>>;

/**
   The connection ID on the chain at position `CHAIN_A` that corresponds to
   the counterparty chain at position `CHAIN_B`.
*/
pub type NthConnectionId<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    DualTagged<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>, ConnectionId>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedConnections<Handle, SIZE> {
    /**
       Get the connection pair for chains at position `CHAIN_A` and `CHAIN_B`,
       which must be less then `SIZE`.
    */
    pub fn connection_at<const CHAIN_A: usize, const CHAIN_B: usize>(
        &self,
    ) -> Result<NthConnectedConnection<CHAIN_A, CHAIN_B, Handle>, Error> {
        if CHAIN_A >= SIZE || CHAIN_B >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get connection beyond position {}/{}",
                CHAIN_A,
                CHAIN_B
            )))
        } else {
            let raw_connection = self.connections[CHAIN_A][CHAIN_B].clone();

            let channel = raw_connection.map_chain(MonoTagged::new, MonoTagged::new);

            Ok(channel)
        }
    }

    pub fn connections(&self) -> &[[ConnectedConnection<Handle, Handle>; SIZE]; SIZE] {
        &self.connections
    }
}

impl<Handle: ChainHandle> DynamicConnectedConnections<Handle> {
    pub fn new(connections: Vec<Vec<ConnectedConnection<Handle, Handle>>>) -> Self {
        Self { connections }
    }

    pub fn connections(&self) -> &Vec<Vec<ConnectedConnection<Handle, Handle>>> {
        &self.connections
    }
}

impl<Handle: ChainHandle, const SIZE: usize> From<ConnectedConnections<Handle, SIZE>>
    for DynamicConnectedConnections<Handle>
{
    fn from(connections: ConnectedConnections<Handle, SIZE>) -> Self {
        DynamicConnectedConnections {
            connections: into_nested_vec(connections.connections),
        }
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedConnections<Handle>>
    for ConnectedConnections<Handle, SIZE>
{
    type Error = Error;

    fn try_from(connections: DynamicConnectedConnections<Handle>) -> Result<Self, Error> {
        Ok(ConnectedConnections {
            connections: try_into_nested_array(connections.connections)?,
        })
    }
}

impl<Handle: ChainHandle> From<ConnectedConnections<Handle, 2>>
    for NthConnectedConnection<0, 1, Handle>
{
    fn from(channels: ConnectedConnections<Handle, 2>) -> Self {
        channels.connection_at::<0, 1>().unwrap()
    }
}

impl<Handle: ChainHandle, const SIZE: usize> ExportEnv for ConnectedConnections<Handle, SIZE> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        for (i, inner_connections) in self.connections.iter().enumerate() {
            for (j, connection_i_to_j) in inner_connections.iter().enumerate() {
                writer.write_env(
                    &format!("CONNECTION_ID_{j}_to_{i}"),
                    &format!("{}", connection_i_to_j.connection_id_a),
                );

                writer.write_env(
                    &format!("CONNECTION_ID_{i}_to_{j}"),
                    &format!("{}", connection_i_to_j.connection_id_b),
                );
            }
        }
    }
}
