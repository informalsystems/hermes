/*!
   Constructs for N-ary connected connections.
*/

use core::convert::TryFrom;
use eyre::eyre;
use ibc::core::ics24_host::identifier::ConnectionId;
use ibc_relayer::chain::handle::ChainHandle;

use super::chains::TaggedHandle;
use crate::error::Error;
use crate::types::binary::connection::ConnectedConnection;
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
   position `FIRST` and `SECOND`.
*/
pub type TaggedConnectedConnection<Handle, const FIRST: usize, const SECOND: usize> =
    ConnectedConnection<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>>;

/**
   The connection ID on the chain at position `FIRST` that corresponds to
   the counterparty chain at position `SECOND`.
*/
pub type TaggedConnectionId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, ConnectionId>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedConnections<Handle, SIZE> {
    /**
       Get the connection pair for chains at position `FIRST` and `SECOND`,
       which must be less then `SIZE`.
    */
    pub fn connection_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedConnectedConnection<Handle, FIRST, SECOND>, Error> {
        if FIRST >= SIZE || SECOND >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get connection beyond position {}/{}",
                FIRST,
                SECOND
            )))
        } else {
            let raw_connection = self.connections[FIRST][SECOND].clone();

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
    for TaggedConnectedConnection<Handle, 0, 1>
{
    fn from(channels: ConnectedConnections<Handle, 2>) -> Self {
        channels.connection_at::<0, 1>().unwrap()
    }
}
