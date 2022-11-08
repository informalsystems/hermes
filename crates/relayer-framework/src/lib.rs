#![no_std]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![doc = include_str!("../README.md")]

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
    developed, known as
    [context-generic programming](https://informalsystems.github.io/context-generic-programming/).

    For a quick introduction, check here for a
    [crash course on context-generic programming](crate::docs::context_generic_programming)

    ## Relayer Variants

    There are currently two variants of relayers supported by the relayer
    framework. The [`base`] or minimal variant provides the base components
    required to implement a minimal version of an IBC relayer. The [`full`]
    variant provides all the additional components that can be used to run
    a full-featured relayer.

    Note that all the components in both [`base`] and [`full`] are implemented
    in a fully modular fashion. As a result, power users can choose to use only
    a subset of components provided by the framework, or introduce new
    components that provide additional functionalities.

*/

mod std_prelude;
extern crate alloc;

#[cfg(doc)]
pub mod docs;

pub mod base;
pub mod full;
