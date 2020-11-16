# TLA+ specification of the IBC Fungible Token Transfer Protocol

A TLA+ specification of the IBC Fungible Token Transfer Protocol ([ICS-020](https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer)).

## Modules

The specification has the following modules: 
  - `ICS20Environment.tla` (the main module)
  - `ICS20Chain.tla`
  - `ICS20Definitions.tla`
  - `PacketHandlers.tla`
  - `FungibleTokenTransferHandlers.tla`
  - `Bank.tla`

The modules `PacketHandlers.tla` and `FungibleTokenTransferHandlers.tla`
capture the main logic of the handlers defined in ICS-020. 
The remaining modules are needed for context.

The module `ICS20Environment.tla` creates instances of 
`ICS20Chain.tla` and encodes the relayer logic. Currently, we have: 
 - two instances of `ICS20Chain.tla`, specifying the behaviors of two chains, `ChainA` and `ChainB`.

The module `ICS20Chain.tla` captures the chain logic relevant to ICS-020. 
It extends the modules `PacketHandlers.tla` and `FungibleTokenTransferHandlers.tla`, which contain definition of operators that handle packet 
datagrams and encode the token transfer application logic, respectively. 
The module `ICS20Definitions.tla` contains definition of operators that are used across all the 
modules.
The module `Bank.tla` encodes operators defined by the bank application.

## Constants

The module `ICS20Environment.tla` is parameterized by the constants:
 - `MaxHeight`, a natural number denoting the maximal height of the chains,
 - `MaxPacketSeq`, a natural number denoting the maximal packet sequence number,
 - `MaxBalance`, a natural number denoting the maximal bank account balance,
 - `NativeDenominationChainA`, a string denoting the native denomination of `ChainA`,
 - `NativeDenominationChainB`, a string denoting the native denomination of `ChainB`

## Properties and invariants

TODO.


## Importing the specification into TLA+ toolbox

To import the specification in the TLA+ toolbox and run TLC:
  - add a new spec in TLA+ toolbox with the root-module file `ICS20Environment.tla` 
  - create a model
  - assign a value to the constants
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - run TLC on the model

## Checking the invariants with Apalache

TODO.
