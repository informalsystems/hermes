#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub mod tests;

#[cfg(any(all(test, feature = "mbt"), doc))]
#[macro_use]
pub mod mbt;
