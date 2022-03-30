/*!
   All test cases are placed within this module.

   We expose the modules as public so that cargo doc
   will pick up the definition by default.
*/

pub mod clear_packet;
pub mod client_expiration;
mod client_settings;
pub mod connection_delay;
pub mod memo;
pub mod supervisor;
pub mod ternary_transfer;
pub mod transfer;

#[cfg(any(doc, feature = "ordered"))]
pub mod ordered_channel;

#[cfg(any(doc, feature = "ica"))]
pub mod ica;

#[cfg(any(doc, feature = "manual"))]
pub mod manual;

#[cfg(any(doc, feature = "example"))]
pub mod example;
