# ADR 008: ICS20 Implementation Proposal

## Status

Accepted

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

#### Keepers and readers

```rust
pub trait ICS20Keeper: ChannelKeeper
+ PortKeeper
+ BankKeeper<AccountId=<Self as Ics20Keeper>::AccountId>
+ AccountKeeper<AccountId=<Self as Ics20Keeper>::AccountId>
{
    /// The account identifier type.
    type AccountId: Into<String>;

    /// Set channel escrow address
    fn set_channel_escrow_address(&mut self, port_id: &PortId, channel_id: &ChannelId) -> Result<(), ICS20Error>;
    /// Sets a new {trace hash -> denom trace} pair to the store.
    fn set_denom_trace(&mut self, denom_trace: DenomTrace) -> Result<(), Ics20Error>;
}

pub trait ICS20Reader: ChannelReader
+ PortReader
+ AccountReader<AccountId=<Self as Ics20Reader>::AccountId>
+ BankReader<AccountId=<Self as Ics20Reader>::AccountId>
{
    /// The account identifier type.
    type AccountId: Into<String> + FromStr<Err=Ics20Error>;

    /// Returns true iff sending is allowed in the module params
    fn is_send_enabled(&self) -> bool;
    /// Returns true iff receiving is allowed in the module params
    fn is_receive_enabled(&self) -> bool;
    /// get_transfer_account returns the ICS20 - transfers AccountId.
    fn get_transfer_account(&self) -> AccountId;
    /// Sets and returns the escrow account id for a port and channel combination
    fn get_channel_escrow_address(&self, port_id: &PortId, channel_id: &ChannelId) -> Result<Self::AccountId, ICS20Error>;
    /// Returns true iff the store contains a `DenomTrace` entry for the specified `HashedDenom`.
    fn has_denom_trace(&self, hashed_denom: HashedDenom) -> bool;
    /// Gets the denom trace associated with the specified hash in the store.
    fn get_denom_trace(&self, denom_hash: HashedDenom) -> Option<DenomTrace>;
}

pub trait BankKeeper {
    /// The account identifier type.
    type AccountId: Into<String>;

    /// This function should enable sending ibc fungible tokens from one account to another
    fn send_coins(&mut self, from: &Self::AccountId, to: &Self::AccountId, amt: Coin) -> Result<(), ICS20Error>;
    /// This function to enable  minting tokens(vouchers) in a module
    fn mint_coins(&mut self, amt: Coin) -> Result<(), ICS20Error>;
    /// This function should enable burning of minted tokens or vouchers
    fn burn_coins(&mut self, module: &Self::AccountId, amt: Coin) -> Result<(), ICS20Error>;
    /// This function should enable transfer of tokens from the ibc module to an account
    fn send_coins_from_module_to_account(
        &mut self,
        module: Self::AccountId,
        to: Self::AccountId,
        amt: Coin,
    ) -> Result<(), Ics20Error>;
    /// This function should enable transfer of tokens from an account to the ibc module
    fn send_coins_from_account_to_module(
        &mut self,
        from: Self::AccountId,
        module: Self::AccountId,
        amt: Coin,
    ) -> Result<(), Ics20Error>;
}

pub trait BankReader {
    /// The account identifier type.
    type AccountId: Into<String> + FromStr;

    /// Returns true if the specified account is not allowed to receive funds and false otherwise.
    fn is_blocked_account(&self, account: &Self::AccountId) -> bool;
}

pub trait AccountReader {
    /// The account identifier type.
    type AccountId: Into<String> + FromStr;

    /// This function should return the account of the ibc module
    fn get_module_account(&self) -> Self::AccountId;
}

pub trait Ics20Context:
Ics20Keeper<AccountId=<Self as Ics20Context>::AccountId>
+ Ics20Reader<AccountId=<Self as Ics20Context>::AccountId>
{
    type AccountId: Into<String> + FromStr<Err=Ics20Error>;
}
```

## Handling ICS20 Packets

ICS20 messages are still a subset of channel packets, so they should be handled as such.

The following handlers are recommended to be implemented in the `ics20_fungible_token_transfer` application in the `ibc`
crate. These handlers will be executed in the module callbacks of any third-party IBC module that is implementing an
ICS20 application on-chain.

```rust
/// Should be used in the transaction that initiates the ICS20 token transfer
/// Performs all logic related to token transfer and returns a SendTransferPacket type
/// for the calling module to create the actual packet and register it in the ibc module.
pub fn send_transfer<Ctx>(ctx: &Ctx, _msg: MsgTransfer) -> Result<SendTransferPacket, ICS20Error>
    where Ctx: ICS20Context
{
    if !ctx.is_send_enabled() {
        return Err(ICS20Error::send_disabled());
    }

    // implementation details, see ICS 20 for reference
}

/// Handles incoming packets with ICS20 data
/// To be called inside the on_recv_packet callback
pub fn on_recv_packet<Ctx>(ctx: &Ctx, _packet: &Packet, _data: &FungibleTokenPacketData) -> ICS20Acknowledgement
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
        ICS20Acknowledgement::Success => Ok(()),
        _ => refund_packet_token(ctx, data)
    }
}

/// Implements logic for refunding a sender on packet timeout or acknowledgement error
pub fn refund_packet_token<Ctx>(_ctx: &Ctx, _data: &FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    //...
}
```


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
