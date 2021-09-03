#[macro_use]
extern crate rouille;

mod config;
pub use config::Config;

pub mod server;

pub(crate) mod handle;
