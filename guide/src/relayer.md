# What is Hermes?

Before we explain what is Hermes, we briefly describe what is a relayer.

A **relayer** is an off-chain process responsible for relaying IBC datagrams between any two chains.
The way it does so is by scanning chain states, building transactions based on these states,
and submitting the transactions.

A relayer is a central element in the IBC network architecture. This is because chain modules 
in this architecture are not directly sending messages to each other over networking infrastructure, but instead they create and store the data to be retrieved and used by a relayer to build the IBC datagrams.


Hermes is a relayer developed in Rust, released under the crate [ibc-relayer-cli](https://crates.io/crates/ibc-relayer-cli). Hermes is actively developed and maintained by
[Informal Systems](https://informal.systems) in the
[ibc-rs](https://github.com/informalsystems/ibc-rs) repository.

We sometimes refer to Hermes as "IBC Relayer CLI", to make it clear that this
is a relayer CLI (i.e., a binary) and distinguish from the relayer core library 
(which is the crate called [`ibc-relayer`](https://crates.io/crates/ibc-relayer)).
