#![no_std]
#![doc = include_str!("../README.md")]

extern crate alloc;

#[cfg(doc)]
pub mod docs;

pub mod impls;
mod std_prelude;
pub mod traits;
pub mod types;
