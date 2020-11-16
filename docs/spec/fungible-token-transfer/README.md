# TLA+ specification of the IBC Fungible Token Transfer Protocol

## The Model

This desribes the TLA+ model of the core logic of the English
specification [ICS
20](https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer). Mirroring
the structure of the English specification we start by discussing
initialization ([Port and Channel Setup & Channel lifecycle management](#port-and-channel-setup-and-channel-lifecycle-management), and then provide the links to the TLA+ modules that
implement [packet relay](#packet-relay), that is, the core callback functions.

As the application "fungible token transfer" uses the underlying IBC
infrastructure, we also modeled it to the extend necessary in [helper modules](#helper-modules)

After that we discuss how to [use the model](#using-the-model), which
includes links to our TLA+ formalization of [Properties and
invariants](#properties-and-invariants). 

### Port and Channel Setup and Channel lifecycle management


In the model we assume that the [`setup()`](https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer#port--channel-setup) functions has been called
before. The [channel handshake
functions]((https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer#channel-lifecycle-management))
are also considered being already executed. Our
model starts from a state where the channel handshake has completed
successfully. 

### Packet Relay

The [core callback functions](https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer#packet-relay)
`createOutgoingPacket()` and `onRecvPacket` and `onRecvPacket` 
	`onTimeoutPacket` as well as the auxiliary function`refundTokens`
	are modeled in
	[FungibleTokenTransferHandlers.tla](FungibleTokenTransferHandlers.tla). 
	
### Helper modules

In order to completely specify the behavior of fungible token
transfer, we encoded the required additional functionalities of IBC in
the TLA+ modules discussed below. From
the viewpoint of TLA+, [ICS20Environment.tla](ICS20Environment.tla) is
the main module that brings together all other modules that are
discussed here. We will discuss it the last.

	
#### [PacketHandlers.tla](PacketHandlers.tla) 

This module captures the functions
specifying packet flow and handling from [ICS
04](https://github.com/cosmos/ics/tree/master/spec/ics-004-channel-and-packet-semantics). 

#### [Bank.tla](bank.tla) 
The bank module encodes functions defined by the Cosmos bank
  application. 
  
#### [ICS20Chain.tla](ICS20Chain.tla)

This module captures the relevant
  Cosmos SDK functionality, that is, the context in which token
  transfer runs. In the complete TLA+ model it is instantiated twice,
  once for each chain participating in the token transfer.
  The transition relation is defined by

```tla
Next ==
    \/ AdvanceChain
    \/ HandlePacketDatagrams
    \/ SendPacket
    \/ AcknowledgePacket
```

- `AdvanceChain` just increments the height of the chain
- `HandlePacketDatagrams`: based on the datagram type of the next
  incoming datagram (created in
  [ICS20Environment.tla](ICS20Environment.tla); see below), it calls the
  appropriate datagram handlers from ICS04
  ([PacketHandlers.tla](PacketHandlers.tla)), which in turn call the
  ICS 20 module callbacks specified in
  [FungibleTokenTransferHandlers.tla](FungibleTokenTransferHandlers.tla).
  This result in an update of the application state (bank accounts,
  packet log, provable and private store).
- `SendPacket` models that a user wants to initiate a transfer
- `AcknowledgePacket` writes an acknowledgement for a received packet
  on the packet log.


#### [ICS20Environment.tla](ICS20Environment.tla) 
This is the main module that
  brings everything together. It specifies a transitions system
  consisting of two chains ([ICS20Chain.tla](ICS20Chain.tla)) and a
  relayer node (modelled here). 
```tla
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
```

- `ChainAction` performs an action of one non-deterministically chosen
  chain.
  
- `EnvironmentAction` performs the relayer logic, that is, reads the
  packet log and creates an appropriate datagram for the destination
  chain (`CreateDatagrams`).
  
## Using the Model

### Constants

The module `ICS20Environment.tla` is parameterized by the constants:
 - `MaxHeight`, a natural number denoting the maximal height of the chains,
 - `MaxPacketSeq`, a natural number denoting the maximal packet sequence number,
 - `MaxBalance`, a natural number denoting the maximal bank account balance,
 - `NativeDenominationChainA`, a string denoting the native denomination of `ChainA`,
 - `NativeDenominationChainB`, a string denoting the native denomination of `ChainB`

### Properties and invariants
TODO.


### Importing the specification into TLA+ toolbox

To import the specification in the TLA+ toolbox and run TLC:
  - add a new spec in TLA+ toolbox with the root-module file `ICS20Environment.tla` 
  - create a model
  - assign a value to the constants
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - run TLC on the model

### Checking the invariant with Apalache

TODO.
