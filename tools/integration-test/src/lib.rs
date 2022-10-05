#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::let_and_return)]

#[cfg(test)]
pub mod tests;

#[cfg(any(all(test, feature = "mbt"), doc))]
#[macro_use]
pub mod mbt;
