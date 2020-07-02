A refactored TLA+ specification of the ICS18 Relayer algorithm.

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

The module `ICS18Environment.tla` is parameterized by the constants:
 - `ClientDatagramsRelayer_i`, for `i \in {1, 2}`, a Boolean flag defining if `Relayer_i` creates client datagrams, 
 - `ConnectionDatagramsRelayer_i`, for `i \in {1, 2}`, a Boolean flag defining if `Relayer_i` creates connection datagrams,
 - `ChannelDatagramsRelayer_i`, for `i \in {1, 2}`, a Boolean flag defining if `Relayer_i` creates channel datagrams,
 - `MaxHeight`, a natural number denoting the maximal height of the chains.

We are interested in verifying three kinds of properties for the relayer algorithm:
- **ICS18Safety**: Bad datagrams are not used to update the chain stores.
- **ICS18Validity**: If `ChainB` receives a datagram from `ChainA`, then the datagram was sent by `ChainA` 
- **ICS18Delivery**: If `ChainA` sends a datagram to `ChainB`, then `ChainB` eventually receives the datagram

Currently, we specify **ICS18Delivery** for all datagrams, and 
**ICS18Safety** for `ClientUpdate` datagrams.

To import the specification in the TLA+ toolbox and run TLC:
  - add a new spec in TLA+ toolbox with the root-module file `ICS18Environment.tla` 
  - create a model
  - assign a value to the constants
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - add the properties `ICS18Safety` and `ICS18Delivery`
  - run TLC on the model
