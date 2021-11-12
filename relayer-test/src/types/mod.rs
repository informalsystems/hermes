/*!
   This module contains definitions of core data structures that are used
   in the test suite.

   A data type belongs to this module if it only comes with the struct
   definition with few methods associated to that struct. If a data
   type has many complicated methods or trait implementations, it
   probably does not belong to here.
*/

pub mod binary;
pub mod config;
pub mod env;
pub mod id;
pub mod nary;
pub mod process;
pub mod single;
pub mod tagged;
pub mod wallet;
