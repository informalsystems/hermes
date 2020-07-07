A TLA+ specification of the Relayer algorithm.

The specification has five modules: 
  - `Relayer.tla` (the main module)
  - `Environment.tla`
  - `ClientHandlers.tla`
  - `ConnectionHandlers.tla`
  - `ChannelHandlers.tla`

The module `Relayer.tla` contains the specification of the relayer algorithm. 
It instantiates the module `Environment.tla`, which takes care of the chain logic. 
The module `Environment.tla` extends the modules `ClientHandlers.tla`, 
`ConnectionHandlers.tla`, and `ChannelHandlers.tla`, which contain definition of 
operators that handle client, connection handshake, and channel handshake
datagrams, respectively.

To import the specification in the TLA+ toolbox and run TLC:
  - add the spec `Relayer.tla` in TLA+ toolbox
  - add `Environment.tla`, `ClientHandlers.tla`, `ConnectionHandlers.tla`, and 
    `ChannelHandlers.tla` as modules in the spec
  - create a model
  - assign a value to the constant `MaxHeight` 
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - add the invariant `Inv` (a conjunction of all the defined invariants)
  - add the property `Prop` (a conjunction of all the defined properties)
  - run TLC on the model
