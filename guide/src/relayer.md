# What is Hermes?

Hermes is an open-source Rust implementation of a relayer for the
[Inter-Blockchain Communication protocol](https://ibc.cosmos.network) (IBC),
released under the [ibc-relayer-cli](https://crates.io/crates/ibc-relayer-cli) crate.

The **Inter-Blockchain Communication protocol** is an end-to-end, connection-oriented,
stateful protocol for reliable, ordered, and authenticated communication between modules
on separate distributed ledgers. [^ibc]

An IBC **relayer** is an off-chain process responsible for relaying IBC messages between any two chains.
The way it does so is by scanning chain states, building transactions based on these states,
and submitting the transactions to the chains involved in the network.

The relayer is a central element in the IBC network architecture. This is because chain modules
in this architecture are not directly sending messages to each other over networking infrastructure,
but instead they create and store the data to be retrieved and used by a relayer to build the IBC messages.

We sometimes refer to Hermes as "IBC Relayer CLI", to make it clear that this
is a relayer CLI (i.e., a binary) and distinguish it from the relayer core library
(that is the crate called [`ibc-relayer`](https://crates.io/crates/ibc-relayer)).

Hermes is actively developed and maintained by [Informal Systems](https://informal.systems) in the [ibc-rs](https://github.com/informalsystems/ibc-rs) repository.

[^ibc]: [The Interblockchain Communication Protocol: An Overview](https://arxiv.org/pdf/2006.15918.pdf)
