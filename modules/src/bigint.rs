#![allow(clippy::assign_op_pattern)]
#![allow(clippy::ptr_offset_with_cast)]

use uint::construct_uint;
pub use uint::FromStrRadixErr;

construct_uint! {
    pub struct U256(4);
}
