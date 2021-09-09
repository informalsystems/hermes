#![allow(clippy::assign_op_pattern)]
#![allow(clippy::ptr_offset_with_cast)]

use uint::construct_uint;

construct_uint! {
    pub struct U256(4);
}
