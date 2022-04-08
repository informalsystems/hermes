use crate::core::ics05_port::capabilities::{Capability, CapabilityName, PortCapability};
use crate::core::ics05_port::error::Error;
use crate::core::ics24_host::identifier::PortId;
use crate::core::ics24_host::path::PortsPath;
use crate::core::ics26_routing::context::ModuleId;
use crate::prelude::*;

/// A context supplying all the necessary read-only dependencies for processing any information regarding a port.
pub trait PortCapabilityReader {
    /// Associated `CapacilityReader`, usually scoped
    type CapabilityReader: CapabilityReader;

    /// Return a reference to the scoped port capability reader
    fn capability_reader(&self) -> &Self::CapabilityReader;

    /// Return the `ModuleId` along with the `PortCapability` associated with a given `PortId`
    fn lookup_module_by_port(&self, port_id: PortId) -> Result<(ModuleId, PortCapability), Error> {
        self.capability_reader()
            .lookup_module(&port_capability_name(port_id))
            .map(|(module_id, capability)| (module_id, capability.into()))
    }

    /// Check if the specified `PortId` is already bound
    fn is_bound(&self, port_id: PortId) -> bool {
        self.get_port_capability(port_id).is_ok()
    }

    /// Get the `PortCapability` associated with the specified `PortId`
    fn get_port_capability(&self, port_id: PortId) -> Result<PortCapability, Error> {
        self.capability_reader()
            .get_capability(&port_capability_name(port_id))
            .map(Into::into)
    }

    /// Authenticate a `PortCapability` against the specified `PortId` by checking if the capability
    /// was previously generated and bound to the specified port
    fn authenticate_port_capability(
        &self,
        port_id: PortId,
        capability: &PortCapability,
    ) -> Result<(), Error> {
        self.capability_reader()
            .authenticate_capability(&port_capability_name(port_id), capability)
    }
}

pub trait PortCapabilityKeeper: PortCapabilityReader {
    /// Associated `CapabilityKeeper`, usually scoped
    type CapabilityKeeper: CapabilityKeeper;

    /// Return a reference to the scoped port capability keeper
    fn capability_keeper(&mut self) -> &mut Self::CapabilityKeeper;

    /// Binds to a port and returns the associated capability
    fn bind_port(&mut self, port_id: PortId) -> Result<PortCapability, Error> {
        if self.is_bound(port_id.clone()) {
            Err(Error::port_already_bound(port_id))
        } else {
            self.capability_keeper()
                .new_capability(port_capability_name(port_id))
                .map(Into::into)
        }
    }
}

pub trait CapabilityKeeper {
    /// Create a new capability with the given name.
    /// Return an error if the capability was already taken.
    fn new_capability(&mut self, name: CapabilityName) -> Result<Capability, Error>;

    /// Claim the specified capability using the specified name.
    /// Return an error if the capability was already taken.
    fn claim_capability(&mut self, name: CapabilityName, capability: Capability);

    /// Release a previously claimed or created capability
    fn release_capability(&mut self, name: CapabilityName, capability: Capability);
}

pub trait CapabilityReader {
    /// Find the `ModuleId` that owns this capability
    fn lookup_module(&self, name: &CapabilityName) -> Result<(ModuleId, Capability), Error>;

    /// Fetch a capability which was previously claimed by specified name
    fn get_capability(&self, name: &CapabilityName) -> Result<Capability, Error>;

    /// Authenticate a given capability and name. Lookup the capability from the internal store and
    /// check against the provided name.
    fn authenticate_capability(
        &self,
        name: &CapabilityName,
        capability: &Capability,
    ) -> Result<(), Error>;

    /// Create a new capability with the given name but don't store it.
    fn create_capability(&self, name: CapabilityName) -> Result<Capability, Error>;
}

fn port_capability_name(port_id: PortId) -> CapabilityName {
    PortsPath(port_id)
        .to_string()
        .parse()
        .expect("PortsPath cannot be empty string")
}

pub struct ScopedCapabilityReader<CR, M> {
    capability_reader: CR,
    module_id: M,
}

impl<CR: CapabilityReader, M: ToString> CapabilityReader for ScopedCapabilityReader<CR, M> {
    fn lookup_module(&self, name: &CapabilityName) -> Result<(ModuleId, Capability), Error> {
        self.capability_reader
            .lookup_module(&name.prefixed_with(self.module_id.to_string()))
    }

    fn get_capability(&self, name: &CapabilityName) -> Result<Capability, Error> {
        self.capability_reader
            .get_capability(&name.prefixed_with(self.module_id.to_string()))
    }

    fn authenticate_capability(
        &self,
        name: &CapabilityName,
        capability: &Capability,
    ) -> Result<(), Error> {
        self.capability_reader
            .authenticate_capability(&name.prefixed_with(self.module_id.to_string()), capability)
    }

    fn create_capability(&self, name: CapabilityName) -> Result<Capability, Error> {
        self.capability_reader
            .create_capability(name.prefixed_with(self.module_id.to_string()))
    }
}

pub struct ScopedCapabilityKeeper<CK, M> {
    capability_keeper: CK,
    module_id: M,
}

impl<CK: CapabilityKeeper, M: ToString> CapabilityKeeper for ScopedCapabilityKeeper<CK, M> {
    fn new_capability(&mut self, name: CapabilityName) -> Result<Capability, Error> {
        self.capability_keeper
            .new_capability(name.prefixed_with(self.module_id.to_string()))
    }

    fn claim_capability(&mut self, name: CapabilityName, capability: Capability) {
        self.capability_keeper
            .claim_capability(name.prefixed_with(self.module_id.to_string()), capability)
    }

    fn release_capability(&mut self, name: CapabilityName, capability: Capability) {
        self.capability_keeper
            .release_capability(name.prefixed_with(self.module_id.to_string()), capability)
    }
}
