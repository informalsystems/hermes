# ADR 007: ICS20 Implementation Proposal

## Changelog

* 21.04.2022: Draft Proposed

## Context

The goal of this ADR is to provide recommendations and a guide for implementing the ICS20 application.

## Decision

The proposal is broken down into traits that should be implemented by the ICS20 module. It also defines some primitives
that would help in building a module compliant with the ICS20 spec.

#### Types

The implementation must provide a base denom type that is serializable to string. Additionally, the following denom
types must also be provided:

* `HashedDenom`: A denom type that can be serialized to a string of the form `'ibc/{Hash(trace_path/base_denom)}'`.
* `PrefixedDenom`: A denom type with a base denom which is prefixed with a trace. The trace itself consists
  of `'{PortId}/{ChannelId}'` pairs and enables coin source tracing[^1].

```rust
/// Base denomination type
pub struct Denom(String);
```

A `Coin` defines a token with a denomination and an amount where the denomination may be any one of the denom types
described above.

```rust
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Coin<Denom> {
    /// Denomination
    pub denom: Denom,
    /// Amount
    pub amount: U256,
}
```

The ICS20 acknowledgement type and packet data type are defined in the spec[^2] and maybe modelled as follows. Note that
these types must be (de)serializable from/to JSON.

```rust
pub enum ICS20Acknowledgement {
    /// Equivalent to b"AQ=="
    Success,
    /// Error Acknowledgement
    Error(String)
}

pub struct FungibleTokenPacketData {
    denomination: Denom,
    amount: U256,
    sender: String,
    receiver: String,
}
```

pub trait ICS20Keeper: ChannelKeeper
+ PortKeeper
+ BankKeeper<Self::AccountId>
+ AccountKeeper<Self::AccountId>
{
    type AccountId: Into<String>;
    /// Returns if sending is allowed in the module params
    fn is_send_enabled(&self) -> bool;
    /// Returns if receiving is allowed in the module params
    fn is_receive_enabled(&self) -> bool;
    /// Set the params (send_enabled and receive_enabled) for the module
    fn set_module_params(&mut self, send_enabled: Option<bool>, receive_enabled: Option<bool>) -> Result<(), ICS20Error>;

    /// The following methods are related to object capabilities.
    ///

    /// Defines a wrapper function for the PortKeeper's bind_port function.
    fn bind_port(&mut self, port_id: &PortId) -> Result<(), ICS20Error>;
    /// Sets the portID for the transfer module.
    fn set_port(&mut self, port_id: &PortId) -> ();
    /// Wraps the CapabilityKeeper's authenticate_capability function
    fn authenticate_capability(&mut self, cap: &PortCapability, name: &CapabilityName) -> bool;
    /// Allows the transfer module to claim a capability that IBC module
    /// passes to it
    fn claim_capability(&mut self, cap: &PortCapability, name: &CapabilityName) -> Result<(), ICS20Error>;
    /// Set channel escrow address
    fn set_channel_escrow_address(&mut self, port_id: &PortId, channel_id: &ChannelId) -> Result<(), ICS20Error>;
}

pub trait ICS20Reader: ChannelReader
+ PortReader
+ AccountReader<Self::AccountId>
{
    type AccountId: From<String>;
    /// is_bound checks if the transfer module is already bound to the desired port.
    fn is_bound(&self, port_id: &PortId) -> bool;
    /// get_transfer_account returns the ICS20 - transfers AccountId.
    fn get_transfer_account(&self) -> AccountId;
    /// get_port returns the portID for the transfer module.
    fn get_port(&self) -> Result<PortId, Error>;
    /// Sets and returns the escrow account id for a port and channel combination
    fn get_channel_escrow_address(&self, port_id: &PortId, channel_id: &ChannelId) -> Result<Self::AccountId, ICS20Error>;
    /// Returns the channel end for port_id and channel_id combination
    fn get_channel(&self, port_id: &PortId, channel_id: &ChannelId) -> Result<ChannelEnd, ICS20Error>;
    /// Returns the next sequence send for port_id and channel_id combination
    fn get_next_sequence_send(&self, port_id: &PortId, channel_id: &ChannelId) -> Result<Sequence, ICS20Error>;
}

pub trait BankKeeper<AccountId> {
    /// This function should enable sending ibc fungible tokens from one account to another
    fn send_coins(&mut self, from: &AccountId, to: &AccountId, amt: &Coin) -> Result<(), ICS20Error>;
    /// This function to enable  minting tokens(vouchers) in a module
    fn mint_coins(&mut self, amt: &Coin) -> Result<(), ICS20Error>;
    /// This function should enable burning of minted tokens or vouchers
    fn burn_coins(&mut self, module: &AccountId, amt: &Coin) -> Result<(), ICS20Error>;
}

pub trait AccountReader<AccountId> {
    /// This function should return the account of the ibc module
    fn get_module_account(&self) -> AccountId;
}

pub trait ICS20Context: ICS20Keeper + ICS20Reader {}
```

## Handling ICS20 Packets

ICS20 messages are still a subset of channel packets, so they should be handled as such.

The following handlers are recommended to be implemented in the `ics20_fungible_token_transfer` application in the `ibc`
crate. These handlers will be executed in the module callbacks of any thirdparty IBC module that is implementing an
ICS20 application on-chain.

```rust
pub enum ICS20Acknowledgement {
    /// Equivalent to b"AQ=="
    Success,
    /// Error Acknowledgement
    Error(String)
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "type")]
pub struct FungibleTokenPacketData {
    denomination: Denom,
    amount: U256,
    sender: String,
    receiver: String,
}


/// Should be used in the transaction that initiates the ICS20 token transfer
/// Performs all logic related to token transfer and returns a SendTransferPacket type
/// for the calling module to create the actual packet and register it in the ibc module.
pub fn send_transfer<Ctx>(ctx: &Ctx, msg: MsgTransfer) -> Result<SendTransferPacket, ICS20Error>
    where Ctx: ICS20Context
{
    if !ctx.is_send_enabled() {
        return Err(ICS20Error::send_disabled());
    }

    // implementation details, see ICS 20 for reference
}

/// Handles incoming packets with ICS20 data
/// To be called inside the on_recv_packet callback
pub fn on_recv_packet<Ctx>(ctx: &Ctx, packet: &Packet, data: &FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    if !ctx.is_received_enabled() {
        return Err(ICS20Error::receive_disabled());
    }

    // implementation details, see ICS 20 for reference
}

/// on_timeout_packet refunds the sender since the original packet sent was
/// never received and has been timed out.
/// To be called inside the on_timeout_packet callback
pub fn on_timeout_packet<Ctx>(ctx: &Ctx, data: &FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    refund_packet_token(ctx, data)
}

/// Responds to the the success or failure of a packet
/// acknowledgement written on the receiving chain. If the acknowledgement
/// was a success then nothing occurs. If the acknowledgement failed, then
/// the sender is refunded their tokens.
/// To be called inside the on_acknowledgement_packet callback
pub fn on_acknowledgement_packet<Ctx>(ctx: &Ctx, ack: ICS20Acknowledgement, data: &FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    match ack {
        ICS20Acknowledgement::Sucess => Ok(()),
        _ => refund_packet_token(ctx, data)
    }
}

/// Implements logic for refunding a sender on packet timeout or acknowledgement error
pub fn refund_packet_token<Ctx>(ctx: &Ctx, data: &FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    //...
}
```

## Status

Proposed

## Consequences

### Positive

- Provides more clarity on the details of implementing the ICS20 application in the `ibc` crate.
- Helps align closer with the ibc-go implementation[^3].

### Negative

### Neutral

## References

[^1]: [ibc-go ADR 001: Coin Source Tracing](https://github.com/cosmos/ibc-go/blob/4271027a5ab1e6faaa2edbc2b9840209c315afab/docs/architecture/adr-001-coin-source-tracing.md)
[^2]: [ICS20 spec](https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer)
[^3]: [ibc-go's transfer module implementation](https://github.com/cosmos/ibc-go/tree/d31f92d9bf709f5550b75db5c70a3b44314d9781/modules/apps/transfer)
