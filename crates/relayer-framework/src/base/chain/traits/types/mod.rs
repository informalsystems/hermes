/*!
   The traits containing the core abstract types for the chain context.

   A chain context is expected to implement at minimum the traits that
   are defined in this module.
*/

pub mod chain;
pub mod event;
pub mod ibc;
pub mod message;

pub use self::chain::HasChainTypes;
pub use self::event::HasEventType;
pub use self::ibc::HasIbcChainTypes;
pub use self::message::HasMessageType;
