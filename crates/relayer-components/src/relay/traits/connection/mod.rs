/*!
    This module contains the trait interfaces for implementing the
    [IBC connection handshake protocol](https://github.com/cosmos/ibc/tree/main/spec/core/ics-003-connection-semantics).
    The protocol establishes a connection between the two participating blockchains.
    This connection between the two chains is necessary in order for channels to be established between them.

    Each of the different `open_*` modules, except for `open_handshake`, defines
    a component responsible for a single step in the handshake protocol.
    The `open_handshake` module wires together the steps that actually constitute
    the handshake protocol proper.
    The `open_init` step is not strictly part of the handshake, as it may be initiated
    by external users; it merely signals the start of the handshake process.

    The relay context only handles the connection handshake initiated in one direction,
    i.e. as initiated by the source chain and acknowledged by the destination chain.
    If a connection is first initialized at the destination chain, it will not be
    handled by this relay context. Instead, it will be handled by the counterpart
    relay context that has the source and destination chains flipped.
*/

pub mod open_ack;
pub mod open_confirm;
pub mod open_handshake;
pub mod open_init;
pub mod open_try;
