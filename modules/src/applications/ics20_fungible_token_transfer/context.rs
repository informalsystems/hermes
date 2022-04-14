use super::error::Error as Ics20Error;
use super::BaseCoin;
use crate::core::ics04_channel::channel::{Counterparty, Order};
use crate::core::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::core::ics04_channel::error::Error as ChannelError;
use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement as GenericAcknowledgement;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics04_channel::Version;
use crate::core::ics05_port::capabilities::{Capability, ChannelCapability};
use crate::core::ics05_port::context::{PortKeeper, PortReader};
use crate::core::ics05_port::error::Error as PortError;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::core::ics26_routing::context::OnRecvPacketAck;
use crate::prelude::*;
use crate::signer::Signer;

pub trait Ics20Keeper:
    ChannelKeeper
    + PortKeeper
    + BankKeeper<AccountId = <Self as Ics20Keeper>::AccountId>
    + AccountReader<AccountId = <Self as Ics20Keeper>::AccountId>
{
    type AccountId: Into<String>;

    /// bind_port defines a wrapper function for the PortKeeper's bind_port function.
    fn bind_port(&self, port_id: PortId) -> Result<(), Ics20Error>;

    /// set_port sets the portID for the transfer module.
    fn set_port(&mut self, port_id: PortId);

    /// authenticate_capability wraps the CapabilityKeeper's authenticate_capability function
    fn authenticate_capability(&self, cap: Capability, name: &str) -> bool;

    /// claim_capability allows the transfer module to claim a capability that IBC module
    /// passes to it
    fn claim_capability(&self, cap: Capability, name: &str) -> Result<(), Ics20Error>;

    /// Set channel escrow address
    fn set_channel_escrow_address(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
    ) -> Result<(), Ics20Error>;
}

pub trait Ics20Reader:
    ChannelReader + PortReader + AccountReader<AccountId = <Self as Ics20Reader>::AccountId>
{
    type AccountId: Into<String>;

    /// is_bound checks if the transfer module is already bound to the desired port.
    fn is_bound(&self, port_id: PortId) -> bool;

    /// get_transfer_account returns the ICS20 - transfers AccountId.
    fn get_transfer_account(&self) -> <Self as Ics20Reader>::AccountId;

    /// get_port returns the portID for the transfer module.
    fn get_port(&self) -> Result<PortId, PortError>;

    /// Returns the escrow account id for a port and channel combination
    fn get_channel_escrow_address(
        &self,
        port_id: PortId,
        channel_id: ChannelId,
    ) -> Result<<Self as Ics20Reader>::AccountId, Ics20Error>;
}

pub trait BankKeeper {
    type AccountId: Into<String>;

    /// This function should enable sending ibc fungible tokens from one account to another
    fn send_coins(
        &self,
        from: Self::AccountId,
        to: Self::AccountId,
        amt: BaseCoin,
    ) -> Result<(), Ics20Error>;

    /// This function to enable minting ibc tokens in a module
    fn mint_coins(&self, module: Self::AccountId, amt: BaseCoin) -> Result<(), Ics20Error>;

    /// This function should enable burning of minted tokens
    fn burn_coins(&self, module: Self::AccountId, amt: BaseCoin) -> Result<(), Ics20Error>;

    /// This function should enable transfer of tokens from the ibc module to an account
    fn send_coins_from_module_to_account(
        &self,
        module: Self::AccountId,
        to: Self::AccountId,
        amt: BaseCoin,
    ) -> Result<(), Ics20Error>;

    /// This function should enable transfer of tokens from an account to the ibc module
    fn send_coins_from_account_to_module(
        &self,
        from: Self::AccountId,
        module: Self::AccountId,
        amt: BaseCoin,
    ) -> Result<(), Ics20Error>;
}

pub trait AccountReader {
    type AccountId: Into<String>;

    /// This function should return the account of the ibc module
    fn get_module_account(&self) -> Self::AccountId;
}

/// Captures all the dependencies which the ICS20 module requires to be able to dispatch and
/// process IBC messages.
pub trait Ics20Context:
    Ics20Keeper<AccountId = <Self as Ics20Context>::AccountId>
    + Ics20Reader<AccountId = <Self as Ics20Context>::AccountId>
{
    type AccountId: Into<String>;
}

#[allow(clippy::too_many_arguments)]
pub fn on_chan_open_init(
    _ctx: &mut impl Ics20Context,
    _order: Order,
    _connection_hops: &[ConnectionId],
    _port_id: &PortId,
    _channel_id: &ChannelId,
    _channel_cap: &ChannelCapability,
    _counterparty: &Counterparty,
    _version: &Version,
) -> Result<(), ChannelError> {
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn on_chan_open_try(
    _ctx: &mut impl Ics20Context,
    _order: Order,
    _connection_hops: &[ConnectionId],
    _port_id: &PortId,
    _channel_id: &ChannelId,
    _channel_cap: &ChannelCapability,
    _counterparty: &Counterparty,
    version: &Version,
    counterparty_version: &Version,
) -> Result<Version, ChannelError> {
    Ok(counterparty_version.clone())
}

pub fn on_chan_open_ack(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
    _counterparty_version: &Version,
) -> Result<(), ChannelError> {
    Ok(())
}

pub fn on_chan_open_confirm(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
) -> Result<(), ChannelError> {
    Ok(())
}

pub fn on_chan_close_init(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
) -> Result<(), ChannelError> {
    Ok(())
}

pub fn on_chan_close_confirm(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
) -> Result<(), ChannelError> {
    Ok(())
}

pub fn on_recv_packet(
    _ctx: &impl Ics20Context,
    _packet: &Packet,
    _relayer: &Signer,
) -> OnRecvPacketAck {
    OnRecvPacketAck::Nil(Box::new(|_| {}))
}

pub fn on_acknowledgement_packet(
    _ctx: &mut impl Ics20Context,
    _packet: &Packet,
    _acknowledgement: &GenericAcknowledgement,
    _relayer: &Signer,
) -> Result<(), ChannelError> {
    Ok(())
}

pub fn on_timeout_packet(
    _ctx: &mut impl Ics20Context,
    _packet: &Packet,
    _relayer: &Signer,
) -> Result<(), ChannelError> {
    Ok(())
}
