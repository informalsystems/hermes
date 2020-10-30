use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};

/// This trait captures all the functional dependencies (i.e., context) which the ICS26 module
/// requires to be able to dispatch messages to their corresponding ICS handler.
pub trait ICS26Context: ClientReader + ClientKeeper + ConnectionReader + ConnectionKeeper {}
