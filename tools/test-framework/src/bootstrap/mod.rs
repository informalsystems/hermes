/*!
   Helper functions for setting up test cases in an imperative way.

   Normal test authors should have no need to call functions provided
   by the `bootstrap` module, as they are implicitly called by the
   [`framework`](crate::framework) constructs.

   Advanced test authors with needs for more flexibility can call
   functions in the `bootstrap` module directly, so that they have
   more control of when exactly new chains and relayers should
   be spawned.
*/

pub mod binary;
pub mod consumer;
pub mod init;
pub mod namada;
pub mod nary;
pub mod single;
