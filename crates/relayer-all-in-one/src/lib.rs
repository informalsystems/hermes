#![no_std]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::needless_lifetimes)]

/*!
    ## Overview

    The IBC relayer framework provides a _fully abstract_ implementation of
    IBC relayer. Users can import this crate as a library to implement a
    concrete relayer instance for use in different use cases and environments.

    There is currently one official concrete implementation of the relayer,
    `ibc-relayer-cosmos`, which implements IBC relaying between two Cosmos
    SDK chains. There are also plans to provide other implementations of the
    relayer, such as support for non-SDK chains and non-Cosmos chains.

    ## Context-Generic Programming

    The IBC relayer framework is implemented using a new design pattern we
    developed, known as _context-generic programming_.

    For a quick introduction, check here for a
    [crash course on context-generic programming](crate::docs::context_generic_programming)

    ## Relayer Variants

    There are currently two variants of relayers supported by the relayer
    framework. The [`base`] or minimal variant provides the base components
    required to implement a minimal version of an IBC relayer. The [`extra`]
    variant provides all the additional components that can be used to run
    a full-featured relayer.

    Note that all the components in both [`base`] and [`extra`] are implemented
    in a fully modular fashion. As a result, power users can choose to use only
    a subset of components provided by the framework, or introduce new
    components that provide additional functionalities.

    ## All-In-One Traits

    The relayer framework provides several
    _[all-in-one traits](crate::docs::context_generic_programming#all-in-one-traits)_
    for users to
    easily implement and use custom relayers. The all-in-one traits are
    configured with a _preset_ list of components, and is best suited
    for users who find the presets to be sufficient.

    A good starting point to learn about the all-in-one traits is to look at
    the _one-for-all_ consumer traits like
    [`OfaBaseChain`](base::one_for_all::traits::chain::OfaBaseChain) and
    [`OfaBaseRelay`](base::one_for_all::traits::relay::OfaBaseRelay).

    There are currently two all-in-one variants of the relayer. The
    [`base`] or minimal variant expose the minimal set of requirements
    that a context needs to implement in order to construct a minimal
    relayer. The [`extra`] variant requires the context to implement
    additional traits, such as
    [OfaFullChain](crate::extra::one_for_all::traits::chain::OfaFullChain),
    in order to construct a full-featured relayer.

    The all-in-one traits provided by the relayer framework for convenience,
    and they are _not_ meant to cover all possible use cases of using the relayer.
    If users want to customize further on how the relayer should
    behave, they can skip the all-in-one traits and make use
    of context-generic programming to implement their own all-in-one
    traits, or to implement the relay context directly by implementing
    the individual traits.

    ## Relayer Framework Internals

    For basic users who just want quick and easy way to creat custom relayers,
    it is usually sufficient to learn how to use the all-in-one traits like
    [`OfaBaseRelay`](base::one_for_all::traits::relay::OfaBaseRelay).
    But for power users who want to have more customization, or developers
    who are maintaining the relayer framework itself, it is necessary to
    have a deeper understanding of how context-generic programming works,
    and explore the individual components that are defined in the
    relayer framework.

    A good starting point to understand the relayer framework internals
    is to look at how abstract types are defined in
    [`HasChainTypes`](ibc_relayer_components::chain::traits::types::chain::HasChainTypes) and
    [`HasRelayTypes`](ibc_relayer_components::relay::traits::types::HasRelayTypes).
    There are also simple components like
    [`CanQueryChainStatus`](ibc_relayer_components::chain::traits::queries::status::CanQueryChainStatus)
    that can be understood as standalone pieces.

    The core logic of IBC relaying is encapsulated behind the
    [`CanRelayPacket`](ibc_relayer_components::relay::traits::packet_relayer::CanRelayPacket) trait.
    The [`FullCycleRelayer`](ibc_relayer_components::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer)
    component is one of the top-level components that performs the full cycle of
    relaying an IBC packet from a source chain to a destination chain.

    A key feature that the relayer framework provides is to allow for
    customization on different strategies of how the messages should be
    submitted to the chain. The
    [`CanSendMessages`](ibc_relayer_components::chain::traits::message_sender::CanSendMessages)
    trait provides the interface for sending messages to a chain. In contrast,
    the [`CanSendIbcMessages`](ibc_relayer_components::relay::traits::ibc_message_sender::CanSendIbcMessages)
    trait provides the interface for sending messages from a _relay_ context. The
    [`SendIbcMessagesWithUpdateClient`](ibc_relayer_components::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
    component is one example of an IBC message sender _middleware_ that attaches
    an UpdateClient message before sending the modified message to a downstream
    message sender.
*/

mod std_prelude;
extern crate alloc;

pub mod all_for_one;
pub mod docs;
pub mod one_for_all;
