/*!
   Code that may belong to the [`ibc_relayer`] module, but are currently
   in this crate for easier review or maintenance.

   Sometimes new constructs are implemented just for testing, and it is
   unclear whether the constructs have more general use that are worth
   provided in the main library, so we put them here so that test authors
   do not get blocked on writing tests.

   There may also be cases where the original code in the main library
   are difficult to be used in a test setting, and we may want to temporarily
   make a copy of the code and modify them in this crate to make it
   easier to be used for testing. We would first do a forked modification
   here so that there are less worry about the behavior of the original
   code being changed due to subtle modifications. The changes can be
   merged back to the main library at a later time once the tests have
   sufficiently proven that the modified code preserve the semantics of
   the original code.
*/

pub mod chain;
pub mod channel;
pub mod connection;
pub mod driver;
pub mod fee;
pub mod foreign_client;
pub mod refresh;
pub mod transfer;
pub mod tx;
