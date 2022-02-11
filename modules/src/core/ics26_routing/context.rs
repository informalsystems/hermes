use crate::prelude::*;

use core::any::Any;
use core::borrow::Borrow;
use core::fmt::Debug;

use crate::applications::ics20_fungible_token_transfer::context::Ics20Context;
use crate::core::ics02_client::context::{ClientKeeper, ClientReader};
use crate::core::ics03_connection::connection::Counterparty;
use crate::core::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::core::ics04_channel::channel::Order;
use crate::core::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics04_channel::Version;
use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics05_port::context::PortReader;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::core::ics26_routing::error::Error;
use crate::signer::Signer;

/// This trait captures all the functional dependencies (i.e., context) which the ICS26 module
/// requires to be able to dispatch and process IBC messages. In other words, this is the
/// representation of a chain from the perspective of the IBC module of that chain.
pub trait Ics26Context:
    ClientReader
    + ClientKeeper
    + ConnectionReader
    + ConnectionKeeper
    + ChannelKeeper
    + ChannelReader
    + PortReader
    + Ics20Context
{
    type Router: Router;

    fn router(&mut self) -> &mut Self::Router;
}

pub trait OnRecvPacketResult {
    fn acknowledgement(&self) -> Acknowledgement;

    fn write_result(&mut self, module: &mut dyn Any);
}

pub trait Module: Debug + Send + Sync + AsAnyMut + 'static {
    #[allow(clippy::too_many_arguments)]
    fn on_chan_open_init(
        &mut self,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: PortId,
        _channel_id: ChannelId,
        _channel_cap: Capability,
        _counterparty: Counterparty,
        _version: Version,
    ) -> Result<(), Error> {
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn on_chan_open_try(
        &mut self,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: PortId,
        _channel_id: ChannelId,
        _channel_cap: Capability,
        _counterparty: Counterparty,
        _counterparty_version: Version,
    ) -> Result<Version, Error>;

    fn on_chan_open_ack(
        &mut self,
        _port_id: PortId,
        _channel_id: ChannelId,
        _counterparty_version: Version,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_chan_open_confirm(
        &mut self,
        _port_id: PortId,
        _channel_id: ChannelId,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_chan_close_init(
        &mut self,
        _port_id: PortId,
        _channel_id: ChannelId,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_chan_close_confirm(
        &mut self,
        _port_id: PortId,
        _channel_id: ChannelId,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_recv_packet(
        &self,
        _packet: Packet,
        _relayer: Signer,
    ) -> Result<Box<dyn OnRecvPacketResult>, Error>;

    fn on_acknowledgement_packet(
        &mut self,
        _packet: Packet,
        _acknowledgement: Acknowledgement,
        _relayer: Signer,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_timeout_packet(&mut self, _packet: Packet, _relayer: Signer) -> Result<(), Error> {
        Ok(())
    }
}

pub trait RouterBuilder: Sized {
    /// The `Router` type that the builder must build
    type Router: Router;

    /// The `ModuleId` type used as the key for the `ModuleId` => `Module` mapping
    type ModuleId;

    /// Registers `Module` against the specified `ModuleId` in the `Router`'s internal map
    ///
    /// Returns an error if a `Module` has already been registered against the specified `ModuleId`
    fn add_route(self, module_id: Self::ModuleId, module: impl Module) -> Result<Self, String>;

    /// Consumes the `RouterBuilder` and returns a `Router` as configured
    fn build(self) -> Self::Router;
}

pub trait AsAnyMut: Any {
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

impl<M: Any + Module> AsAnyMut for M {
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// A router maintains a mapping of `ModuleId`s against `Modules`. Implementations must not publicly
/// expose APIs to add new routes once constructed. Routes may only be added at the time of
/// instantiation using the `RouterBuilder`.
pub trait Router {
    type ModuleId: ?Sized;

    /// Returns a mutable reference to a `Module` registered against the specified `ModuleId`
    fn get_route_mut(&mut self, module_id: impl Borrow<Self::ModuleId>) -> Option<&mut dyn Module>;

    /// Returns true if the `Router` has a `Module` registered against the specified `ModuleId`
    fn has_route(&self, module_id: impl Borrow<Self::ModuleId>) -> bool;
}
