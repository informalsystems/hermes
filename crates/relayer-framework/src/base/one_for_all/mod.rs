//! An abstract trait which stipulates all of dependencies that an application
//! needs to provide in order to make use of the functionality the framework
//! exposes.
//!
//! There is a duality between the `one_for_all` trait and the [`all_for_one`]
//! trait such that types that implement the `one_for_all` trait gain access to
//! the APIs exposed by the `all_for_one` trait. The `one_for_all` trait
//! encapsulates what functionality applications need to provide. The
//! `all_for_one` trait encapsulates what functionality applications have
//! access to and can use once the `one_for_all` trait is implemented.
//!
//! This is trait is meant to be the main trait that users of the framework
//! implement in order to use the APIs provided by the framework, which are
//! encapsulated in the `all_for_one` trait.

pub mod components;
pub mod impls;
pub mod instances;
pub mod traits;
