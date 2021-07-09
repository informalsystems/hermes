use std::collections::HashMap;
use tracing::debug;

use crate::object;
use crate::registry::Registry;
use anomaly::BoxError;
use ibc::ics02_client::client_state::{AnyClientState, ClientState};
use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics04_channel::error::Kind;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::Height;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Permission {
    Allow,
    Deny,
}

impl Permission {
    fn and(self, other: &Permission) -> Permission {
        if matches!(self, Permission::Allow) && matches!(other, Permission::Allow) {
            self
        } else {
            Permission::Deny
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum CacheKey {
    Client(ChainId, ClientId),
    Channel(ChainId, PortId, ChannelId),
    Connection(ChainId, ConnectionId),
}

/// A cache storing filtering status (allow or deny) for
/// arbitrary identifiers.
#[derive(Default, Debug)]
pub(crate) struct FilterPolicy {
    /// A cache associating a generic identifying key, such as
    /// client id, channel id, or connection id, with an
    /// [`Allowed`] status.
    permission_cache: HashMap<CacheKey, Permission>,
}

impl FilterPolicy {
    /// Given a connection end and the underlying client for that
    /// connection, controls both the client as well as the
    /// client on the counterparty chain.
    /// Returns `true` if both clients are allowed, `false` otherwise.
    /// Caches the result for both clients as well as the connection.
    pub fn control_connection_end_and_client(
        &mut self,
        registry: &mut Registry,
        client_state: &AnyClientState,
        connection: &ConnectionEnd,
        connection_id: &ConnectionId,
    ) -> Result<Permission, BoxError> {
        // Fetch the details of the client on counterparty chain.
        let counterparty_chain_id = client_state.chain_id();
        let counterparty_chain = registry.get_or_spawn(&counterparty_chain_id)?;
        let counterparty_client_id = connection.counterparty().client_id();
        let counterparty_client_state =
            counterparty_chain.query_client_state(&counterparty_client_id, Height::zero())?;

        // Figure out the identifier of the connection
        let id_conn = CacheKey::from((client_state.chain_id(), connection_id.clone()));

        // Control both clients, cache their results.
        let client_control = self.control_client(&connection.client_id(), &client_state);
        let counterparty_client_control =
            self.control_client(&counterparty_client_id, &counterparty_client_state);
        let permission = client_control.and(&counterparty_client_control);

        debug!(
            "\t [filter] relay for conn ? {:?}: {:?}",
            id_conn, permission
        );
        // Save the connection id in the cache
        self.permission_cache.entry(id_conn).or_insert(permission);

        Ok(permission)
    }

    /// Given a client identifier and its corresponding client state,
    /// controls the client state and decides if the client should
    /// be allowed or not.
    /// Returns `true` if client is allowed, `false` otherwise.
    /// Caches the result.
    pub fn control_client(&mut self, client_id: &ClientId, state: &AnyClientState) -> Permission {
        let identifier = CacheKey::from((state.chain_id(), client_id.clone()));

        let permission = match state.trust_threshold() {
            Some(trust) if trust.numerator == 1 && trust.denominator == 3 => Permission::Allow,
            _ => Permission::Deny,
        };

        debug!(
            "\t [filter] relay for client ? {:?}: {:?}",
            state, permission
        );
        self.permission_cache
            .entry(identifier)
            .or_insert(permission);

        permission
    }

    pub fn control_client_object(
        &mut self,
        registry: &mut Registry,
        obj: &object::Client,
    ) -> Result<Permission, BoxError> {
        let chain = registry.get_or_spawn(&obj.dst_chain_id)?;
        debug!(
            "\t [filter] deciding if to relay on {:?} hosted chain {}",
            obj.dst_client_id, obj.dst_chain_id
        );
        let client_state = chain.query_client_state(&obj.dst_client_id, Height::zero())?;
        Ok(self.control_client(&obj.dst_client_id, &client_state))
    }

    pub fn control_conn_object(
        &mut self,
        registry: &mut Registry,
        obj: &object::Connection,
    ) -> Result<Permission, BoxError> {
        let src_chain = registry.get_or_spawn(&obj.src_chain_id)?;
        debug!(
            "\t [filter] deciding if to relay on {:?} hosted on chain {}",
            obj, obj.src_chain_id
        );
        let connection_end = src_chain.query_connection(&obj.src_connection_id, Height::zero())?;
        let client_state =
            src_chain.query_client_state(&connection_end.client_id(), Height::zero())?;

        self.control_connection_end_and_client(
            registry,
            &client_state,
            &connection_end,
            &obj.src_connection_id,
        )
    }

    fn control_channel(
        &mut self,
        registry: &mut Registry,
        chain_id: &ChainId,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Permission, BoxError> {
        let src_chain = registry.get_or_spawn(&chain_id)?;
        debug!(
            "\t [filter] deciding if to relay on {}/{} hosted on chain {}",
            port_id, channel_id, chain_id
        );
        let channel_end = src_chain.query_channel(&port_id, &channel_id, Height::zero())?;
        let conn_id = channel_end.connection_hops.first().ok_or_else(|| {
            Kind::InvalidConnectionHopsLength(1, channel_end.connection_hops().len())
        })?;
        let connection_end = src_chain.query_connection(conn_id, Height::zero())?;
        let client_state =
            src_chain.query_client_state(&connection_end.client_id(), Height::zero())?;

        let permission = self.control_connection_end_and_client(
            registry,
            &client_state,
            &connection_end,
            &conn_id,
        )?;

        let key = CacheKey::from((chain_id.clone(), port_id.clone(), channel_id.clone()));
        debug!(
            "\t [filter] relay for channel ? {:?}: {:?}",
            key, permission
        );
        self.permission_cache.entry(key).or_insert(permission);

        Ok(permission)
    }

    pub fn control_chan_object(
        &mut self,
        registry: &mut Registry,
        obj: &object::Channel,
    ) -> Result<Permission, BoxError> {
        self.control_channel(
            registry,
            &obj.src_chain_id,
            &obj.src_port_id,
            &obj.src_channel_id,
        )
    }

    pub fn control_uni_chan_path_object(
        &mut self,
        registry: &mut Registry,
        obj: &object::UnidirectionalChannelPath,
    ) -> Result<Permission, BoxError> {
        self.control_channel(
            registry,
            &obj.src_chain_id,
            &obj.src_port_id,
            &obj.src_channel_id,
        )
    }
}

impl From<(ChainId, ClientId)> for CacheKey {
    fn from(source: (ChainId, ClientId)) -> CacheKey {
        CacheKey::Client(source.0, source.1)
    }
}

impl From<(ChainId, ConnectionId)> for CacheKey {
    fn from(source: (ChainId, ConnectionId)) -> CacheKey {
        CacheKey::Connection(source.0, source.1)
    }
}

impl From<(ChainId, PortId, ChannelId)> for CacheKey {
    fn from(source: (ChainId, PortId, ChannelId)) -> Self {
        CacheKey::Channel(source.0, source.1, source.2)
    }
}
