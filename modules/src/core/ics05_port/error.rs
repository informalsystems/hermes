use crate::core::ics05_port::capabilities::CapabilityName;
use crate::core::ics24_host::identifier::PortId;

use flex_error::define_error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
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

        CapabilityAlreadyTaken
            { capability_name: CapabilityName }
            | e | { format_args!("capability for '{0}' is already taken", e.capability_name) },

        CapabilityMismatch
            { capability_name: CapabilityName }
            | e | { format_args!("capability name '{0}' not mapped to given capability", e.capability_name) },

        CapabilityMappingNotFound
            | _ | { "capability mapping was not found" },

        CapabilityNotOwned
            | _ | { "capability isn't owned by any module" },

        ImplementationSpecific
            | _ | { "implementation specific error" },
    }
}
