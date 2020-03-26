A TLA+ specification of the Relayer algorithm.

The specification has two modules: 
  - `relayer.tla` (the main module)
  - `environment.tla` (the environment module)

The module `relayer.tla` contains the specification of the relayer algorithm. It instantiates the module `environment.tla`, which takes care of the chain logic. Currently, the relayer and the environment can only handle ICS 002 Client datagrams.

To import the specification in the TLA+ toolbox and run TLC:
  - add the spec `relayer.tla` in TLA+ toolbox
  - add `environment.tla` as a module in the spec
  - create a model
  - assign a value to the constant `MaxHeight` 
  - choose "Temporal formula" as the behavior spec, and use the formula `Spec`
  - add the invariants `Inv` (a conjunction of the invariants `TypeOK`, `CreateClientInv`, `ClientUpdateInv`)
  - add the properties `CreateClientIsGenerated`, `Env!ClientCreated`, `Env!ClientUpdated`, `Env!HeightsDontDecrease`
  - run TLC on the model
