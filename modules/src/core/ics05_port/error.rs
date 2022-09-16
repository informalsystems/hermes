use crate::{core::ics24_host::identifier::PortId, prelude::*};
use flex_error::define_error;

define_error! {
	#[derive(Debug, PartialEq, Eq, derive_more::From)]
	Error {
		UnknownPort
			{ port_id: PortId }
			| e | { format_args!("port '{0}' is unknown", e.port_id) },

		PortAlreadyBound
			{ port_id: PortId }
			| e | { format_args!("port '{0}' is already bound", e.port_id) },

		ModuleNotFound
			{ port_id: PortId }
			| e | { format_args!("could not retrieve module from port '{0}'", e.port_id) },

		ImplementationSpecific
			{ reason: String }
			| e | { format_args!("implementation specific error: {}", e.reason) },
	}
}
