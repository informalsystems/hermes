# ADR 008: ICS20 Implementation

## Changelog
* 16.02.2022: Proposed

## Context

The goal of this ADR, is to provide recommendations for implementing the ICS20 application

## Decision
The  implementation is broken down into traits which should be implemented by the application
context, it also outlines some struct definitions that would facilitate identification of some ibc primitives.

There are a couple handlers that should be implemented in this also to help users of the library to build ICS20 compliant
on-chain modules

```rust
    pub enum ICS20Error{
        InvalidDenomTrace,
        ...
    }

    /// This struct and it's implementations should help identifying denomination traces
    pub struct DenomTrace {
        /// Full denomination path
        trace_path: String,
        /// Base denimination
        base_denom: String
    }

    impl DenomTrace {
        /// Creates a denom trace from a raw string
        pub fn parse_denom_trace(raw_trace: &str) -> Self {
            ...
        }
        /// Returns the full denom path
        fn get_full_denom_path(&self) -> String {
            ...
        }
        /// Validates the denom trace fields
        fn validate(&self) -> Result<(), ICS20Error> {
            ...
        }
        /// IBCDenom a coin denomination for an ICS20 fungible token in the format
        /// 'ibc/trace_path/base_denom'. If the trace is empty, it will return the base denomination.
        fn ibc_denom(&self) -> String {
            ...
        }
        /// Returns the prefix for this trace
        fn get_prefix(&self) -> String {
            ...
        }
    }
    
    type Coin = ibc_proto::cosmos::base::v1beta1::Coin;

    pub trait ICS20Keeper<AccountId: Into<String>>: 
        ChannelKeeper 
        + PortKeeper 
        + PortReader 
        + BankKeeper<AccountId> 
        + AccountKeeper<AccountId> 
        + CapabilityKeeper 
    {
        /// bind_port defines a wrapper function for the PortKeeper's bind_port function.
        fn bind_port(&self, port_id: PortId) -> Result<(), ICS20Error>;
        /// set_port sets the portID for the transfer module.
        fn set_port(&self, port_id: PortId) -> ();
        /// authenticate_capability wraps the CapabilityKeeper's authenticate_capability function
        fn authenticate_capability(&self, cap: Capability, name: &str) -> bool;
        /// claim_capability allows the transfer module to claim a capability that IBC module
        /// passes to it
        fn claim_capability(&self, cap: Capability, name: &str) -> Result<(), ICS20Error>;
    }

    pub trait ICS20Reader<AccountId: Into<String>>:
    PortReader
    + AccountReader<AccountId>
    {
        /// is_bound checks if the transfer module is already bound to the desired port.
        fn is_bound(&self, port_id: PortId) -> bool;
        /// get_transfer_account returns the ICS20 - transfers AccountId.
        fn get_transfer_account(&self) -> AccountId;
        /// get_port returns the portID for the transfer module.
        fn get_port(&self) -> Result<PortId, Error>;
    }

    pub trait BankKeeper<AccountId: Into<String>> {
        /// This function should enable sending ibc fungible tokens from one account to another
        fn send_coins(&self, from: AccountId, to: AccountId, amt: Coin) -> Result<(), ICS20Error>;
        /// This function to enable  minting ibc tokens in a module
        fn mint_coins(&self, module: AccountId, amt: Coin) -> Result<(), ICS20Error>;
        /// This function should enable burning of minted tokens
        fn burn_coins(&self, module: AccountId, amt: Coin) -> Result<(), ICS20Error>;
        /// This function should enable transfer of tokens from the ibc module to an account
        fn send_coins_from_module_to_account(&self, module: AccountId, to: AccountId, amt: Coin) -> Result<(), ICS20Error>;
        /// This function should enable transfer of tokens from an account to the ibc module
        fn send_coins_from_account_to_module(&self, from: AccountId, module: AccountId, amt: Coin) -> Result<(), ICS20Error>;
    }

    pub trait AccountReader<AccountId: Into<String>> {
        /// This function should return the account of the ibc module
        fn get_module_account(&self) -> AccountId;
        /// Returns the escrow account id for a port and channel combination
        fn get_escrow_account(port_id: PortId, channel_id: ChannelId) -> AccountId;
    }

    pub trait ICS20Context: ICS20Keeper + ICS20Reader;
```
## Handling ICS20 Packets
ICS20 messages are still a subset of channel packets so they should be handled as such

The following handlers are recommended to be implemented in the ics20_fungible_token_transfer application in the ibc-rs crate

These handlers will be executed in the module callbacks of any thirdparty IBCmodule that is implementing an ICS20 application on-chain
```rust
    /// Initiates ICS20 token transfer
    /// Escrows tokens from sender and registers the send packet 
    pub send_transfer<Ctx>(ctx: &Ctx, source_port: PortId, msg: MsgTransfer) -> Result<(), ICS20Error>
        where Ctx: ICS20Context
    {
        /* 
            ICS20 Application Logic
            ...
        */
    }
    
    /// Handles incoming packets with ICS20 data
    pub on_recv_packet<Ctx>(ctx: &Ctx, packet: Packet, data: MsgTransfer) -> Result<(), ICS20Error>
        where Ctx: ICS20Context
    {
        /* 
            ICS20 Application Logic
            ...
         */
    }

    /// on_timeout_packet refunds the sender since the original packet sent was
    /// never received and has been timed out.
    pub on_timeout_packet<Ctx>(ctx: &Ctx, packet: Packet, data: MsgTransfer) -> Result<(), ICS20Error>
        where Ctx: ICS20Context
    {
        /* 
            ICS20 Application Logic
            ...
        */
    }
    /// on_acknowledgement_packet responds to the the success or failure of a packet
    /// acknowledgement written on the receiving chain. If the acknowledgement
    /// was a success then nothing occurs. If the acknowledgement failed, then
    /// the sender is refunded their tokens.
    pub on_acknowledgement_packet<Ctx>(ctx: &Ctx, packet: Packet, data: MsgTransfer) -> Result<(), ICS20Error>
        where Ctx: ICS20Context
    {
        /* 
            ICS20 Application Logic
            ...
        */
    }

    /// Implements logic for refunding a sender on packet timeout or acknowledgement error
    pub refund_packet_token<Ctx>(ctx: &Ctx, packet: Packet, data: MsgTransfer) -> Result<(), ICS20Error>
      where Ctx: ICS20Context
    {
        /* 
            ICS20 Application Logic
            ...
        */
    }
```

## Status

Proposed

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive

### Negative

### Neutral

## References

* https://github.com/informalsystems/ibc-rs/issues/1759
* https://github.com/cosmos/ibc-go/tree/d31f92d9bf709f5550b75db5c70a3b44314d9781/modules/apps/transfer
