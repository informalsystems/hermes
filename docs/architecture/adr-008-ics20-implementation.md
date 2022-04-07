# ADR 008: ICS20 Implementation

## Changelog
* 16.02.2022: Proposed

## Context

The goal of this ADR, is to provide recommendations and a guide for implementing the ICS20 application

## Decision
The  implementation is broken down into traits which should be implemented by the ICS20 module
context, it also defines some primitives that would help in building a module compliant with the ICS20 spec.

Decided it's better for the ICS20 context to be completely independent of the ibc core context traits, that way it can be 
fully implemented as a standalone module in any framework.

Coupling the ICS20 Context with the ibc Core traits will not allow the existence of the ICS20 module as a standalone library in some frameworks
It should be upto the module implementer to use the provided helper functions and ICS20 primitives correctly

```rust
    define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidDenomTrace
            | _ | { "Denom trace is not valid" },

        SendDisabled
            | _ | { "Sending tokens is disabled" },
        ReceiveDisabled
            | _ | { "Receiving tokens is disabled" },
        }
    }
    #[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
    #[serde(untagged)]
    pub struct Denom(String);
    
    impl AsRef<&str> for Denom {
        fn as_ref(&self) -> &str{
            self.0.as_str()
        }
    }

    impl FromStr for Denom{
        fn from_str(val: &str) -> Self {
            Self(val.to_string())
        }
    }

    /// Coin defines a token with a denomination and an amount.
    #[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
    pub struct Coin {
        /// Denomination
        pub denom: DenomTrace,

        /// Amount
        pub amount: U256,
    }

    pub struct TracePrefix {
        pub port_id: PortId,
        pub channel_id: ChannelId
    }

    /// This struct and it's implementations should help identifying denomination traces
    pub struct DenomTrace {
        /// Full denomination path
        pub trace_path: Vec<TracePrefix>,
        /// Base denimination
        pub base_denom: Denom
    }

    impl DenomTrace {
        /// Returns the full denom path
        fn get_full_denom_path(&self) -> String {
            self.trace_path.into_iter().fold(String::new(), |acc, val| {
                let next = Self::get_denom_prefix(&val.port_id, &val.channel_id);
                format!("{}{}", acc, next)
            })
        }
        /// IBCDenom a coin denomination for an ICS20 fungible token in the format
        /// 'ibc/trace_path/base_denom'. If the trace is empty, it will return the base denomination.
        fn ibc_denom(&self) -> String {
            format!("ibc/{}", self.get_full_denom_path())
        }
        /// Returns the prefix for this trace
        fn get_prefix(&self) -> String {
            DenomTrace::get_denom_prefix(self.trace_path[0].port_id, self.trace_path[0].channel_id)
        }

        /// Returns the prefix for this trace
        pub fn has_prefix(denom: String, prefix: String) -> bool {
            denom.starts_with(prefix)
        }

        /// get_denom_prefix returns the receiving denomination prefix
        pub fn get_denom_prefix(port_id: &PortId, channel_id: &ChannelId) -> String {
            format!("{}/{}/", port_id, channel_id)
        }


        /// get_prefixed_denom returns the denomination with the port_id and channel_id prefixed
        pub fn get_prefixed_denom(port_id: &PortId, channel_id: &ChannelId, base_denom: String) -> String {
            format!("{}/{}/{}", port_id, channel_id, base_denom)
        }
        
        pub fn parse_denom_trace(denom: &str) -> Result<Self, ICS20Error> {
            
        }
    }

    impl FromStr for DenomTrace {
        type Error = ICS20Error
        fn from_str(val: &str) -> Result<Self, Self::Error> {
            DenomTrace::parse_denom_trace(val)
        }
    }

    /// sender_chain_is_source returns false if the denomination originally came
    /// from the receiving chain and true otherwise.
    fn sender_chain_is_source(source_port: &PortId, source_channel: &ChannelId, denom: String) -> bool {
        // This is the prefix that would have been prefixed to the denomination
        // on sender chain IF and only if the token originally came from the
        // receiving chain.

        !receiver_chain_is_source(source_port, source_channel, denom)
    }

    /// receiver_chain_is_source returns true if the denomination originally came
    /// from the receiving chain and false otherwise.
    fn receiver_chain_is_source(source_port: &PortId, source_channel: &ChannelId, denom: String) -> bool {
        // The prefix passed in should contain the SourcePort and SourceChannel.
        // If  the receiver chain originally sent the token to the sender chain
        // the denom will have the sender's SourcePort and SourceChannel as the
        // prefix.

        let voucher_prefix = get_denom_prefix(source_port, source_channel);
        DenomTrace::has_prefix(denom, voucher_prefix)

    }

    pub trait ICS20Keeper: BankKeeper<Self::AccountId> 
        + AccountKeeper<Self::AccountId>
    {
        type AccountId: Into<String>;
        /// Returns if sending is allowed in the module params
        fn is_send_enabled(&self) -> bool;
        /// Returns if receiving is allowed in the module params
        fn is_receive_enabled(&self) -> bool;
        /// Set the params (send_enabled and receive_enabled) for the module
        fn set_module_params(send_enabled: Option<bool>, receive_enabled: Option<bool>) -> Result<(), ICS20Error>;
        /// bind_port defines a wrapper function for the PortKeeper's bind_port function.
        fn bind_port(&self, port_id: PortId) -> Result<(), ICS20Error>;
        /// set_port sets the portID for the transfer module.
        fn set_port(&self, port_id: PortId) -> ();
        /// authenticate_capability wraps the CapabilityKeeper's authenticate_capability function
        fn authenticate_capability(&self, cap: PortCapability, name: CapabilityName) -> bool;
        /// claim_capability allows the transfer module to claim a capability that IBC module
        /// passes to it
        fn claim_capability(&self, cap: PortCapability, name: CapabilityName) -> Result<(), ICS20Error>;
        /// Set channel escrow address
        fn set_channel_escrow_address(&self, port_id: PortId, channel_id: ChannelId) -> Result<(), ICS20Error>;
    }

    pub trait ICS20Reader:
     AccountReader<Self::AccountId>
    {
        type AccountId: From<String>;
        /// is_bound checks if the transfer module is already bound to the desired port.
        fn is_bound(&self, port_id: PortId) -> bool;
        /// get_transfer_account returns the ICS20 - transfers AccountId.
        fn get_transfer_account(&self) -> AccountId;
        /// get_port returns the portID for the transfer module.
        fn get_port(&self) -> Result<PortId, Error>;
        /// Sets and returns the escrow account id for a port and channel combination
        fn get_channel_escrow_address(&self, port_id: PortId, channel_id: ChannelId) -> Result<Self::AccountId, ICS20Error>;
        /// Returns the channel end for port_id and channel_id combination
        fn get_channel(port_id: PortId, channel_id: ChannelId) -> Result<ChannelEnd, ICS20Error>;
        /// Returns the next sequence send for port_id and channel_id combination
        fn get_next_sequence_send(port_id: PortId, channel_id: ChannelId) -> Result<Sequence, ICS20Error>;
    }

    pub trait BankKeeper<AccountId> {
        /// This function should enable sending ibc fungible tokens from one account to another
        fn send_coins(&self, from: AccountId, to: AccountId, amt: Coin) -> Result<(), ICS20Error>;
        /// This function to enable  minting tokens(vouchers) in a module
        fn mint_coins(&self, amt: Coin) -> Result<(), ICS20Error>;
        /// This function should enable burning of minted tokens or vouchers
        fn burn_coins(&self, module: AccountId, amt: Coin) -> Result<(), ICS20Error>;
    }

    pub trait AccountReader<AccountId> {
        /// This function should return the account of the ibc module
        fn get_module_account(&self) -> AccountId;
    }

    pub trait ICS20Context: ICS20Keeper + ICS20Reader {}
```
## Handling ICS20 Packets
ICS20 messages are still a subset of channel packets so they should be handled as such

The following handlers are recommended to be implemented in the ics20_fungible_token_transfer application in the ibc-rs crate

These handlers will be executed in the module callbacks of any thirdparty IBCmodule that is implementing an ICS20 application on-chain

```rust
    pub enum ICS20Acknowledgement {
    /// Equivalent to b"AQ=="
    Success,
    /// Error Acknowledgement
    Error(String)
}

impl From<GenericAcknowledgement> for ICS20Acknowledgement {
    ...
}

impl Acknowledgement for ICS20Acknowledgement {
    fn success() -> bool {
        ...
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "type")]
pub struct FungibleTokenPacketData {
    denomination: Denom,
    amount: U256,
    sender: String,
    receiver: String,
}

impl FungibleTokenPacketData {
    pub fn new(denom: &str, amount: &str, sender: &str, receive: &str) -> Result<Self, ICS20Error> {
        // Validate inputs and create self
    }

    pub fn get_bytes(&self) -> Result<Vec<u8>, ICS20Error> {
        // serialize to json and encode to bytes
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct MsgTransfer {
    /// the port on which the packet will be sent
    pub source_port: PortId,
    /// the channel by which the packet will be sent
    pub source_channel: ChannelId,
    /// the tokens to be transferred
    pub token: Coin,
    /// the sender address
    pub sender: Signer,
    /// the recipient address on the destination chain
    pub receiver: Signer,
    /// Timeout height relative to the current block height.
    /// The timeout is disabled when set to 0.
    pub timeout_height: Height,
    /// Timeout timestamp relative to the current block timestamp.
    /// The timeout is disabled when set to 0.
    pub timeout_timestamp: Timestamp,
}

#[derive(Serialize, Deserialize)]
pub struct SendTransferPacket {
    pub data: FungibleTokenPacketData,
    pub source_port: PortId,
    pub source_channel: ChannelId,
    pub destination_port: PortId,
    pub destination_channel: ChannelId,
    pub sequence: Sequence,
    /// Timeout height offset relative to the current block height.
    pub timeout_offset_height: Height,
    /// Timeout timestamp offset from the current timestamp
    pub timeout_offset_timestamp: Timestamp,
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

    let source_channel_end = ctx.get_channel_end(&(msg.source_port.clone(), msg.source_channel.clone()))?;
    let destination_port = source_channel_end.counterparty().port_id();
    let destination_channel = source_channel_end.counterparty().channel_id()
        .ok_or(|_| ICS20Error::channel_error("counterparty channel not found"))?;

    let sequence = ctx.get_next_sequence_send(&(msg.source_port.clone(), msg.source_channel.clone()))?;
    
    let full_denom_path = msg.token.denom.get_full_denom_path();

    if sender_chain_is_source(&msg.source_port, &msg.source_channel, full_denom_path.clone()) {
        let escrow_address = ctx.get_channel_escrow_address(msg.source_port.clone(), msg.source_channel.clone())?;

        // Send tokens from sender to channel escrow
        ctx.send_coins(msg.sender.as_str().into(), escrow_address, msg.token)?;
    } else {
        let module_acc = ctx.get_module_account();
        // Send tokens to module
        ctx.send_coins(msg.sender.as_str().into(), module_acc, msg.token)?;
        // Burn tokens
        ctx.burn_coins(module_acc, msg.token)?;
    }

    let data = FungibleTokenPacketData::new(full_denom_path, msg.token.amount, msg.sender.as_str(), msg.receiver.as_str())?;
    SendTransferPacket {
        data,
        source_port: msg.source_port,
        source_channel: msg.source_channel,
        destination_port,
        destination_channel,
        sequence,
        timeout_offset_height: msg.timeout_height,
        timeout_offset_timestamp: msg.timeout_timestamp
    }
}

/// Handles incoming packets with ICS20 data
/// To be called inside the on_recv_packet callback
pub fn on_recv_packet<Ctx>(ctx: &Ctx, packet: Packet, data: FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    if !ctx.is_received_enabled() {
        return Err(ICS20Error::receive_disabled());
    }

    let full_denom_path = data.denomination.to_string();
    if receiver_chain_is_source(&packet.dest_port, &packet.dest_channel, full_denom_path.clone()) {
        
        // remove prefix added by sender chain
        let voucher_prefix = get_denom_prefix(&packet.source_port, &packet.source_channel);
        let unprefixed_denom = full_denom_path.clone().split_off(voucher_prefix.len());
        
        let denom = parse_denom_trace(&unprefixed_denom)?;
        
        let token = Coin {
            denom,
            amount: data.amount
        };

        let escrow_address = ctx.get_channel_escrow_address(packet.dest_port.clone(), packet.dest_channel.clone())?;
        // Send tokens from escrow to receiver
        ctx.send_coins(escrow_address, data.receiver.into())?;
        
        return Ok(())
    }

    let denom = get_denom_prefix(&packet.dest_port, &packet.dest_channel);
    // NOTE: source_prefix contains the trailing "/"
    denom.push_str(full_denom_path);
    
    let token = Coin {
        denom: DenomTrace::parse_denom_trace(&denom)?,
        amount: data.amount
    };
    
    let module_acc = ctx.get_module_account();
    // Mint vouchers to module
    ctx.mint_coins(token.clone())?;
    // Send vouchers to receiver
    ctx.send_coins(module_acc, data.receiver.into())?;
    Ok(())
    
}

/// on_timeout_packet refunds the sender since the original packet sent was
/// never received and has been timed out.
/// To be called inside the on_timeout_packet callback
pub fn on_timeout_packet<Ctx>(ctx: &Ctx, packet: Packet, data: FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    refund_packet_token(ctx, data)
}

/// on_acknowledgement_packet responds to the the success or failure of a packet
/// acknowledgement written on the receiving chain. If the acknowledgement
/// was a success then nothing occurs. If the acknowledgement failed, then
/// the sender is refunded their tokens.
/// To be called inside the on_acknowledgement_packet callback
pub fn on_acknowledgement_packet<Ctx>(ctx: &Ctx, ack: ICS20Acknowledgement, data: FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    match ack {
        ICS20Acknowledgement::Sucess => Ok(()),
        _ => refund_packet_token(ctx, data)
    }
}

/// Implements logic for refunding a sender on packet timeout or acknowledgement error
pub fn refund_packet_token<Ctx>(ctx: &Ctx, data: FungibleTokenPacketData) -> Result<(), ICS20Error>
    where Ctx: ICS20Context
{
    let full_denom_path = data.denomination.to_string();

    let token = Coin {
        denom: DenomTrace::parse_denom_trace(&full_denom_path)?,
        amount: data.amount
    };
    if sender_chain_is_source(&packet.source_port, &packet.source_channel, full_denom_path.clone()) {
        let escrow_address = ctx.get_channel_escrow_address(packet.source_port.clone(), packet.source_channel.clone())?;
        
        ctx.send_coins(escrow_address, data.sender.into(), token.clone())?;
        return Ok(())
    }
    
    // Mint vouchers back to sender
    ctx.mint_coins(token.clone())?;
    // Send back to sender
    let module_acc = ctx.get_module_account()?;
    ctx.send_coins(module_acc, data.sender.into(), token)?;
    Ok(())
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
