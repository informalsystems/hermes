use alloc::format;

use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics05_port::error::Error;
use crate::core::ics24_host::identifier::PortId;
use crate::core::ics24_host::path::PortsPath;

// A context supplying all the necessary read-only dependencies for processing any information regarding a port.
pub trait PortReader: CapabilityReader {
    fn lookup_module_by_port(&self, port_id: &PortId) -> Result<Capability, Error>;

    fn is_bound(&self, port_id: PortId) -> bool {
        self.get_capability(format!("{}", PortsPath(port_id)))
            .is_ok()
    }

    fn authenticate(&self, port_id: PortId, capability: &Capability) -> bool {
        self.authenticate_capability(format!("{}", PortsPath(port_id)), capability)
            .is_ok()
    }
}

pub trait PortKeeper: CapabilityKeeper + PortReader {
    fn bind_port(&mut self, port_id: PortId) -> Result<Capability, Error> {
        if self.is_bound(port_id.clone()) {
            Err(Error::port_already_bound(port_id))
        } else {
            self.new_capability(format!("{}", PortsPath(port_id)))
        }
    }
}

pub trait CapabilityKeeper {
    fn new_capability(&mut self, name: impl AsRef<str>) -> Result<Capability, Error>;

    fn claim_capability(&mut self, name: impl AsRef<str>, capability: Capability);

    fn release_capability(&mut self, name: impl AsRef<str>, capability: Capability);
}

pub trait CapabilityReader {
    fn get_capability(&self, name: impl AsRef<str>) -> Result<Capability, Error>;

    fn authenticate_capability(
        &self,
        name: impl AsRef<str>,
        capability: &Capability,
    ) -> Result<(), Error>;
}
