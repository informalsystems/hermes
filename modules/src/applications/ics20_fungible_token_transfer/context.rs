use super::error::Error as Ics20Error;
use super::BaseCoin;
use crate::core::ics04_channel::channel::{Counterparty, Order};
use crate::core::ics04_channel::context::{ChannelKeeper, ChannelReader};
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
    type AccountId: Into<String> + FromStr<Err = Ics20Error>;

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
    ) -> Result<<Self as Ics20Reader>::AccountId, Ics20Error> {
        // https://github.com/cosmos/cosmos-sdk/blob/master/docs/architecture/adr-028-public-key-addresses.md
        let contents = format!("{}/{}", port_id, channel_id);
        let mut hasher = Sha256::new();
        hasher.update(VERSION.as_bytes());
        hasher.update(b"0");
        hasher.update(contents.as_bytes());
        let hash: Vec<u8> = hasher.finalize().to_vec().drain(20..).collect();
        String::from_utf8(hex::encode_upper(hash))
            .expect("hex encoded bytes are not valid UTF8")
            .parse()
    }

    /// Returns true iff send is enabled.
    fn is_send_enabled(&self) -> bool;

    /// Returns true iff receive is enabled.
    fn is_receive_enabled(&self) -> bool;
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

fn validate_transfer_channel_params(
    _ctx: &mut impl Ics20Context,
    order: Order,
    _port_id: &PortId,
    channel_id: &ChannelId,
    version: &Version,
) -> Result<(), Ics20Error> {
    if channel_id.sequence() > (u32::MAX as u64) {
        return Err(Ics20Error::chan_seq_exceeds_limit(channel_id.sequence()));
    }

    if order != Order::Unordered {
        return Err(Ics20Error::channel_not_unordered(order));
    }

    // TODO(hu55a1n1): check that port_id matches the port_id that the transfer module is bound to

    if version != &Version::ics20() {
        return Err(Ics20Error::invalid_version(version.clone()));
    }

    Ok(())
}

fn validate_counterparty_version(counterparty_version: &Version) -> Result<(), Ics20Error> {
    if counterparty_version == &Version::ics20() {
        Ok(())
    } else {
        Err(Ics20Error::invalid_counterparty_version(
            counterparty_version.clone(),
        ))
    }
}

#[allow(clippy::too_many_arguments)]
pub fn on_chan_open_init(
    ctx: &mut impl Ics20Context,
    order: Order,
    _connection_hops: &[ConnectionId],
    port_id: &PortId,
    channel_id: &ChannelId,
    _channel_cap: &ChannelCapability,
    _counterparty: &Counterparty,
    version: &Version,
) -> Result<(), Ics20Error> {
    validate_transfer_channel_params(ctx, order, port_id, channel_id, version)?;

    // TODO(hu55a1n1): claim channel capability

    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn on_chan_open_try(
    ctx: &mut impl Ics20Context,
    order: Order,
    _connection_hops: &[ConnectionId],
    port_id: &PortId,
    channel_id: &ChannelId,
    _channel_cap: &ChannelCapability,
    _counterparty: &Counterparty,
    version: &Version,
    counterparty_version: &Version,
) -> Result<Version, Ics20Error> {
    validate_transfer_channel_params(ctx, order, port_id, channel_id, version)?;
    validate_counterparty_version(counterparty_version)?;

    // TODO(hu55a1n1): claim channel capability (iff we don't already own it)

    Ok(Version::ics20())
}

pub fn on_chan_open_ack(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
    counterparty_version: &Version,
) -> Result<(), Ics20Error> {
    validate_counterparty_version(counterparty_version)?;
    Ok(())
}

pub fn on_chan_open_confirm(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
) -> Result<(), Ics20Error> {
    Ok(())
}

pub fn on_chan_close_init(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
) -> Result<(), Ics20Error> {
    Err(Ics20Error::cant_close_channel())
}

pub fn on_chan_close_confirm(
    _ctx: &mut impl Ics20Context,
    _port_id: &PortId,
    _channel_id: &ChannelId,
) -> Result<(), Ics20Error> {
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
) -> Result<(), Ics20Error> {
    Ok(())
}

pub fn on_timeout_packet(
    _ctx: &mut impl Ics20Context,
    _packet: &Packet,
    _relayer: &Signer,
) -> Result<(), Ics20Error> {
    Ok(())
}
