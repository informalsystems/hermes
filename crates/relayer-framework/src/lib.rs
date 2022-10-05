#![no_std]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![doc = include_str!("../README.md")]

extern crate alloc;

#[cfg(doc)]
pub mod docs;

mod std_prelude;

pub mod addons;
pub mod all_for_one;
pub mod core;
pub mod one_for_all;
