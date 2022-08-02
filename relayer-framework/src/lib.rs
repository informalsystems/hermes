#![no_std]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![doc = include_str!("../README.md")]

extern crate alloc;

#[cfg(doc)]
pub mod docs;

pub mod impls;
pub mod instances;
mod std_prelude;
pub mod traits;
pub mod types;
