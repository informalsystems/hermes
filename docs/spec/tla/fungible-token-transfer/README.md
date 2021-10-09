# TLA+ specification of the IBC Fungible Token Transfer Protocol

This document describes the TLA+ model of the core logic of the English
specification [ICS
20](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-020-fungible-token-transfer). We
start by discussing [the model of the
protocol](#the-model-of-the-protocol).
 Then this document provides links to our TLA+ formalization of [Properties and
invariants](#properties-and-invariants) that formalizes what a fungible
token protocol is supposed to achieve. 
After that we discuss how to [use the model](#using-the-model).

## The Model of the Protocol

 Mirroring
the structure of the English specification, we start by discussing
initialization ([Port and Channel Setup & Channel lifecycle management](#port-and-channel-setup-and-channel-lifecycle-management)), and then provide the links to the TLA+ modules that
implement [packet relay](#packet-relay), that is, the core callback functions.

As the application "fungible token transfer" uses the underlying IBC
infrastructure, we also modeled it to the extent necessary in [helper
modules](#helper-modules).

### Port and Channel Setup and Channel lifecycle management


In the model we assume that the [`setup()`](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-020-fungible-token-transfer#port--channel-setup) function has been called
before. The [channel handshake
functions](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-020-fungible-token-transfer#channel-lifecycle-management)
are also considered being already executed. Our
model starts from a state where the channel handshake has completed
successfully. 

### Packet Relay

The [core callback functions](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-020-fungible-token-transfer#packet-relay)
`createOutgoingPacket()`, `onRecvPacket()`, `onRecvPacket()` and 
	`onTimeoutPacket()`, as well as the auxiliary function `refundTokens()`
	are modeled in
	[ICS20FungibleTokenTransferHandlers.tla](ICS20FungibleTokenTransferHandlers.tla). 
	
### Helper modules

In order to completely specify the behavior of fungible token
transfer, we encoded the required additional functionalities of IBC in
the TLA+ modules discussed below. From
the viewpoint of TLA+, [IBCTokenTransfer.tla](IBCTokenTransfer.tla) is
the main module that brings together all other modules that are
discussed here. We will discuss it the last.

	
#### [ICS04PacketHandlers.tla](ICS04PacketHandlers.tla) 

This module captures the functions
specifying packet flow and handling from [ICS
04](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-004-channel-and-packet-semantics). 

#### [Bank.tla](Bank.tla) 
The bank module encodes functions defined by the Cosmos bank
  application. 
  
#### [Chain.tla](Chain.tla)

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

- `AdvanceChain`: increments the height of the chain
- `HandlePacketDatagrams`: based on the datagram type of the next
  incoming datagram (created in
  [IBCTokenTransfer.tla](IBCTokenTransfer.tla); see below), it calls the
  appropriate datagram handlers from ICS 04
  ([ICS04PacketHandlers.tla](ICS04PacketHandlers.tla)), which in turn call the
  ICS 20 module callbacks specified in
  [ICS20FungibleTokenTransferHandlers.tla](ICS20FungibleTokenTransferHandlers.tla).
  This result in an update of the application state (bank accounts,
  packet log, provable and private store).
- `SendPacket`: models that a user wants to initiate a transfer
- `AcknowledgePacket`: writes an acknowledgement for a received packet
  on the packet log.


#### [IBCTokenTransfer.tla](IBCTokenTransfer.tla) 
This is the main module that
  brings everything together. It specifies a transitions system
  consisting of two chains ([Chain.tla](Chain.tla)) and a
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
  

### Properties and invariants

The English specification provides informal requirements as "[desired properties](
https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-020-fungible-token-transfer#desired-properties)".

#### Preservation of fungibility

We understand that for establishing "Preservation of fungibility" it
is sufficient to establish that if
some tokens have been transferred from chain A to chain B, and the receiver
on chain B wants to return them, then the tokens can be returned.

For this we require the assumption (which is somewhat implicit it
 its [correctness
argument](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-020-fungible-token-transfer#correctness)) that the source chain only performs valid transitions.

This is implemented in the property `ICS20Prop` in the file [IBCTokenTransfer.tla](IBCTokenTransfer.tla).


#### Preservation of total supply

We understand "Preservation of total supply" as conjunction of two
properties

- For each native denomination of a chain: the sum of the amounts in
  user accounts in this denomination and the amounts in escrow
  accounts in this denomination is constant.
  
The following intuitive property can only be specified and guaranteed
if all involved chains only perform valid transitions:
  
- The amount in denomination *d* in escrow accounts in the chain in which *d* is native
is equal to the sum of:
	* the amounts in-flight packets in a (prefixed or unprefixed) denomination ending with *d*
	* the amounts in accounts in a prefixed denomination ending with *d*, in which *d* is 
**not**  native

These two properties are implemented in the invariant `ICS20Inv` in the file 
[IBCTokenTransfer.tla](IBCTokenTransfer.tla).

#### No Whitelist

This is a design requirement, and not a correctness property that can be expressed 
in temporal logic.


#### Symmetric

This is not a temporal property but a property on the local transition
relation. It is satisfied by construction (of both the code and the
model).


#### No Byzantine Inflation

This should be implied by the first property of preservation of total
supply. This is under the assumption that the property found in ICS 20
"Fault containment: prevents Byzantine-inflation of tokens originating
on chain A, as a result of chain B’s Byzantine behavior (though any
users who sent tokens to chain B may be at risk)." is purely
understood in terms on inflation **on chain A**.

We note that chain B can send an unbounded amount of tokens that it
claims to originate from A to some chain C.


## Using the Model


### Constants

The module `IBCTokenTransfer.tla` is parameterized by the constants:
 - `MaxHeight`, a natural number denoting the maximal height of the chains,
 - `MaxPacketSeq`, a natural number denoting the maximal packet sequence number,
 - `MaxBalance`, a natural number denoting the maximal bank account balance,
 - `NativeDenominationChainA`, a string denoting the native denomination of `ChainA`,
 - `NativeDenominationChainB`, a string denoting the native denomination of `ChainB`

 We assume that the native denominations of the chains are different.


### Importing the specification into TLA+ toolbox

To import the specification in the TLA+ toolbox and run TLC:
  - add a new spec in TLA+ toolbox with the root-module file `IBCTokenTransfer.tla` 
  - create a model
  - assign a value to the constants (example values can be found in `IBCTokenTransfer.cfg`)
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - run TLC on the model

#### Basic checks with TLC

We ran TLC using the constants defined in `IBCTokenTransfer.cfg` and verified the invariants `TypeOK` and `ICS20Inv` in 1min21s and the property `ICS20Prop` in 9min34s.
We note that the specification currently models two transfers: one from `ChainA` to `ChainB`, and vice versa, in their respective native denominations.  
Both chains are correct, and there is no malicious relayer. 
The relayer implements the logic from [ICS 18](https://github.com/cosmos/ibc/tree/5877197dc03e844542cb8628dd52674a37ca6ff9/spec/ics-018-relayer-algorithms), in particular, it does not 
relay timeouts. 
However, the packet timeout handlers are specified in [`ICS04PacketHandlers.tla`](ICS04PacketHandlers.tla)
for future use.

#### Apalache

The specification contains type annotations for the 
model checker [Apalache](https://github.com/informalsystems/apalache).
The specification passes the type check using the type checker [Snowcat](https://apalache.informal.systems/docs/apalache/typechecker-snowcat.html) 
integrated in Apalache.  
