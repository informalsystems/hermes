// #![deny(warnings)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::ptr_arg)]
#![doc = include_str!("../README.md")]

//!
//! ## Overview
//! 
//! This IBC test framework gives developers working on relayer software in Rust a robust
//! yet flexible suite of functionality to test the correctness of their relayer implementations,
//! as well as verify the expected state of chains in response to relayed messages and packets.
//! 
//! ## Example Test 
//! 
//! Here's an example of a simple test that showcases some of the important features that the 
//! framework exposes:
//! 
//! ```rust
//! use ibc_integration_test::prelude::*;
//! 
//! pub struct ExampleTest;
//! 
//! #[test]
//! pub fn example_test() -> Result<(), Error> {
//!     run_binary_channel_test(&ExampleTest)
//! }
//! 
//! impl TestOverrides for ExampleTest {}
//! 
//! impl BinaryChannelTest for ExampleTest {
//!     fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
//!         &self,
//!         _config: &TestConfig,
//!         _relayer: RelayerDriver,
//!         _chains: ConnectedChains<ChainA, ChainB>,
//!         _channel: ConnectedChannel<ChainA, ChainB>,
//!     ) -> Result<(), Error> {
//!         suspend()
//!     }
//! }
//! ```
//! 
//! The `example_test` function is the top-most function that drives the test itself. The top-
//! most test function typically does nothing more than to specify what kind of test we want 
//! to run. In the case of this example, we're running a 
//! [`BinaryChannelTest`](ibc_test_framework::framework::binary::channel::BinaryChannelTest),
//! which sets up a relayer instance between two chains connected via channels. 
//! 
//! Note that the `run_binary_channel_test` (and indeed every `run_*` test function) takes as
//! its single parameter an empty struct that represents the test case. 

extern crate alloc;

pub mod bootstrap;
pub mod chain;
pub mod error;
pub mod framework;
pub mod ibc;
pub mod prelude;
pub mod relayer;
pub mod types;
pub mod util;
