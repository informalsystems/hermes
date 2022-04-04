use crate::prelude::*;

use alloc::borrow::{Borrow, Cow};
use core::any::Any;
use core::fmt::Debug;
use core::{fmt, str::FromStr};

use crate::applications::ics20_fungible_token_transfer::context::Ics20Context;
use crate::core::ics02_client::context::{ClientKeeper, ClientReader};
use crate::core::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::core::ics04_channel::channel::{Counterparty, Order};
use crate::core::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement as GenericAcknowledgement;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics04_channel::Version;
use crate::core::ics05_port::capabilities::ChannelCapability;
use crate::core::ics05_port::context::PortReader;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::events::IbcEvent;
use crate::handler::HandlerOutput;
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

    fn router(&self) -> &Self::Router;

    fn router_mut(&mut self) -> &mut Self::Router;
}

#[derive(Debug, PartialEq)]
pub struct InvalidModuleId;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModuleId(String);

impl ModuleId {
    pub fn new(s: Cow<'_, str>) -> Result<Self, InvalidModuleId> {
        if !s.trim().is_empty() && s.chars().all(char::is_alphanumeric) {
            Ok(Self(s.into_owned()))
        } else {
            Err(InvalidModuleId)
        }
    }
}

impl fmt::Display for ModuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for ModuleId {
    type Err = InvalidModuleId;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(Cow::Borrowed(s))
    }
}

impl Borrow<str> for ModuleId {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}

/// Types implementing this trait are expected to implement `From<GenericAcknowledgement>`
pub trait Acknowledgement: AsRef<[u8]> {}

pub type WriteFn = dyn FnOnce(&mut dyn Any);

pub enum OnRecvPacketAck {
    Nil(Box<WriteFn>),
    Successful(Box<dyn Acknowledgement>, Box<WriteFn>),
    Failed(Box<dyn Acknowledgement>),
}

pub type ModuleEvent = IbcEvent;

pub type ModuleOutput = HandlerOutput<(), ModuleEvent>;

pub trait Module: Debug + Send + Sync + AsAnyMut + 'static {
    #[allow(clippy::too_many_arguments)]
    fn on_chan_open_init(
        &mut self,
        _output: &mut ModuleOutput,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _channel_cap: &ChannelCapability,
        _counterparty: &Counterparty,
        _version: &Version,
    ) -> Result<(), Error> {
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn on_chan_open_try(
        &mut self,
        _output: &mut ModuleOutput,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _channel_cap: &ChannelCapability,
        _counterparty: &Counterparty,
        _counterparty_version: &Version,
    ) -> Result<Version, Error>;

    fn on_chan_open_ack(
        &mut self,
        _output: &mut ModuleOutput,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _counterparty_version: &Version,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_chan_open_confirm(
        &mut self,
        _output: &mut ModuleOutput,
        _port_id: &PortId,
        _channel_id: &ChannelId,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_chan_close_init(
        &mut self,
        _output: &mut ModuleOutput,
        _port_id: &PortId,
        _channel_id: &ChannelId,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_chan_close_confirm(
        &mut self,
        _output: &mut ModuleOutput,
        _port_id: &PortId,
        _channel_id: &ChannelId,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_recv_packet(
        &self,
        _output: &mut ModuleOutput,
        _packet: &Packet,
        _relayer: &Signer,
    ) -> OnRecvPacketAck {
        OnRecvPacketAck::Nil(Box::new(|_| {}))
    }

    fn on_acknowledgement_packet(
        &mut self,
        _output: &mut ModuleOutput,
        _packet: &Packet,
        _acknowledgement: &GenericAcknowledgement,
        _relayer: &Signer,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn on_timeout_packet(
        &mut self,
        _output: &mut ModuleOutput,
        _packet: &Packet,
        _relayer: &Signer,
    ) -> Result<(), Error> {
        Ok(())
    }
}

pub trait RouterBuilder: Sized {
    /// The `Router` type that the builder must build
    type Router: Router;

    /// Registers `Module` against the specified `ModuleId` in the `Router`'s internal map
    ///
    /// Returns an error if a `Module` has already been registered against the specified `ModuleId`
    fn add_route(self, module_id: ModuleId, module: impl Module) -> Result<Self, String>;

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
    /// Returns a mutable reference to a `Module` registered against the specified `ModuleId`
    fn get_route_mut(&mut self, module_id: &impl Borrow<ModuleId>) -> Option<&mut dyn Module>;

    /// Returns true if the `Router` has a `Module` registered against the specified `ModuleId`
    fn has_route(&self, module_id: &impl Borrow<ModuleId>) -> bool;
}
