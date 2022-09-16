pub use core::prelude::v1::*;

// Re-export according to alloc::prelude::v1 because it is not yet stabilized
// https://doc.rust-lang.org/src/alloc/prelude/v1.rs.html
pub use alloc::{
	borrow::ToOwned,
	boxed::Box,
	string::{String, ToString},
	vec::Vec,
};

pub use alloc::{format, vec};

// Those are exported by default in the std prelude in Rust 2021
pub use core::{
	convert::{TryFrom, TryInto},
	iter::FromIterator,
};
