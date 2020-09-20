# TLA+ specification of the IBC Relayer

A TLA+ specification of the ICS18 Relayer algorithm.

## Modules

The specification has seven modules: 
  - `ICS18Environment.tla` (the main module)
  - `Relayer.tla` 
  - `Chain.tla`
  - `ClientHandlers.tla`
  - `ConnectionHandlers.tla`
  - `ChannelHandlers.tla`
  - `RelayerDefinitions.tla`

The module `ICS18Environment.tla` creates instances of `Relayer.tla` and 
`Chain.tla`. Currently, we have 
 - two instances of `Relayer.tla`, specifying the behavior of two correct relayers, `Relayer1` and `Relayer2`,
 - two instances of `Chain.tla`, specifying the behaviors of two chains, `ChainA` and `ChainB`.

The module `Relayer.tla` contains the specification of the relayer algorithm. 
The module `Chain.tla` captures the chain logic. 
It extends the modules `ClientHandlers.tla`, 
`ConnectionHandlers.tla`, and `ChannelHandlers.tla`, which contain definition of 
operators that handle client, connection handshake, and channel handshake
datagrams, respectively.
The module `RelayerDefinitions.tla` contains definition of operators that are used across all the 
modules.

## Constants

The module `ICS18Environment.tla` is parameterized by the constants:
 - `ClientDatagramsRelayer_i`, for `i in {1, 2}`, a Boolean flag defining if `Relayer_i` creates client datagrams, 
 - `ConnectionDatagramsRelayer_i`, for `i in {1, 2}`, a Boolean flag defining if `Relayer_i` creates connection datagrams,
 - `ChannelDatagramsRelayer_i`, for `i in {1, 2}`, a Boolean flag defining if `Relayer_i` creates channel datagrams,
 - `MaxHeight`, a natural number denoting the maximal height of the chains,
 - `ChannelOrdering`, a string indicating whether the channels are ordered or unordered 

## Properties

We are interested in verifying three kinds of properties for the relayer algorithm:
- **ICS18Safety**: Bad datagrams are not used to update the chain stores.
- **ICS18Validity**: If `ChainB` receives a datagram from `ChainA`, then the datagram was sent by `ChainA` 
- **ICS18Delivery**: If `ChainA` sends a datagram to `ChainB`, then `ChainB` eventually receives the datagram

## Invariants
To check invariants with [Apalache](https://github.com/informalsystems/apalache/), we introduce a history variable, which keeps track of the state of the connections 
and channels.
We define the invariant **ICS18Inv**, which states that 
once a connection or channel end reaches a certain state, 
it does not go back to the previous state. 

For example, if the connection end on `ChainA` has 
reached state `OPEN`, it never goes back to the state `UNINIT`.


## Importing the specification into TLA+ toolbox

To import the specification in the TLA+ toolbox and run TLC:
  - add a new spec in TLA+ toolbox with the root-module file `ICS18Environment.tla` 
  - create a model
  - assign a value to the constants
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - add the properties `ICS18Safety` and `ICS18Delivery`
  - run TLC on the model
  
#### Assigning values to the constants in a TLC model

The Boolean flags, defined as constants in the module `ICS18Environment.tla`, allow us to run experiments in different settings. For example, if we set both `ClientDatagramsRelayer_1` and `ClientDatagramsRelayer_2` to `TRUE` in a TLC model, then the two relayers in the system concurrently create datagrams related to client creation and client update, and the model checker will check the temporal properties related to client datagrams. 

Observe that the setting where, for example,  `ClientDatagramsRelayer_1 = TRUE`, `ConnectionDatagramsRelayer_2 = TRUE`, `ChannelDatagramsRelayer_1 = TRUE`, and the remaining flags are `FALSE`, is equivalent to  a single relayer, as there is no concurrency in the creation of datagrams between the two relayers. 

## Checking the invariant `ICS18Inv` with Apalache

To check the `ICS18Environment.tla` specification with [Apalache](https://github.com/informalsystems/apalache/), we use the file `ICS18Environment_apalache`, where we define the values of the model constants. To run the model checker and check the invariant `ICS18Inv`, we run the command:
```shell
apalache check --inv=ICS18Inv ICS18Environment_apalache.tla
```