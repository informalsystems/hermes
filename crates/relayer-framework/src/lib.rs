#![no_std]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![doc = include_str!("../README.md")]

extern crate alloc;

#[cfg(test)]
extern crate std;

#[cfg(test)]
pub mod tests;

#[cfg(doc)]
pub mod docs;

mod std_prelude;

pub mod base;
pub mod common;
pub mod full;
