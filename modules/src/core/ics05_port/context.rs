use alloc::format;

use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics05_port::error::Error;
use crate::core::ics24_host::identifier::PortId;
use crate::core::ics24_host::path::PortsPath;

/// A context supplying all the necessary read-only dependencies for processing any information regarding a port.
pub trait PortReader: CapabilityReader {
    /// Module Id type that can be mapped to an ICS26 router callback module
    type ModuleId;

    /// Return the module_id along with the capability associated with a given port_id
    fn lookup_module_by_port(
        &self,
        port_id: &PortId,
    ) -> Result<(Self::ModuleId, Capability), Error>;

    /// Check if the specified port_id is already bounded
    fn is_bound(&self, port_id: PortId) -> bool {
        self.get_capability(format!("{}", PortsPath(port_id)))
            .is_ok()
    }

    /// Authenticate a capability key against a port_id by checking if the capability was previously
    /// generated and bound to the specified port
    fn authenticate(&self, port_id: PortId, capability: &Capability) -> bool {
        self.authenticate_capability(format!("{}", PortsPath(port_id)), capability)
            .is_ok()
    }
}

pub trait PortKeeper: CapabilityKeeper + PortReader {
    /// Binds to a port and returns the associated capability
    fn bind_port(&mut self, port_id: PortId) -> Result<Capability, Error> {
        if self.is_bound(port_id.clone()) {
            Err(Error::port_already_bound(port_id))
        } else {
            self.new_capability(format!("{}", PortsPath(port_id)))
        }
    }
}

pub trait CapabilityKeeper {
    /// Create a new capability with the given name.
    /// Return an error if the capability was already taken.
    fn new_capability(&mut self, name: impl AsRef<str>) -> Result<Capability, Error>;

    /// Claim the specified capability using the specified name.
    /// Return an error if the capability was already taken.
    fn claim_capability(&mut self, name: impl AsRef<str>, capability: Capability);

    /// Release a previously claimed or created capability
    fn release_capability(&mut self, name: impl AsRef<str>, capability: Capability);
}

pub trait CapabilityReader {
    /// Fetch a capability which was previously claimed by specified name
    fn get_capability(&self, name: impl AsRef<str>) -> Result<Capability, Error>;

    /// Authenticate a given capability and name. Lookup the capability from the internal store and
    /// check against the provided name.
    fn authenticate_capability(
        &self,
        name: impl AsRef<str>,
        capability: &Capability,
    ) -> Result<(), Error>;
}
