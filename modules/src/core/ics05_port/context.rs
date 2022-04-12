use crate::core::ics05_port::capabilities::{Capability, CapabilityName};
use crate::core::ics05_port::error::Error;
use crate::core::ics24_host::identifier::PortId;
use crate::core::ics24_host::path::PortsPath;
use crate::core::ics26_routing::context::ModuleId;
use crate::prelude::*;

/// A context supplying all the necessary read-only dependencies for processing any information regarding a port.
pub trait PortCapabilityReader<M: Into<ModuleId>>: CapabilityReader<M> {
    /// Return the `ModuleId` along with the `Capability` associated with a given `PortId`
    fn lookup_module_by_port(
        &self,
        port_id: PortId,
    ) -> Result<(ModuleId, Self::Capability), Error> {
        self.lookup_module(&port_capability_name(port_id))
            .map(|(module_id, capability)| (module_id, capability))
    }

    /// Check if the specified `PortId` is already bound
    fn is_bound(&self, port_id: PortId) -> bool {
        self.get_port_capability(port_id).is_ok()
    }

    /// Get the `Capability` associated with the specified `PortId`
    fn get_port_capability(&self, port_id: PortId) -> Result<Self::Capability, Error> {
        self.get_capability(&port_capability_name(port_id))
    }

    /// Authenticate a `Capability` against the specified `PortId` by checking if the capability
    /// was previously generated and bound to the specified port
    fn authenticate_port_capability(
        &self,
        port_id: PortId,
        capability: &Self::Capability,
    ) -> Result<(), Error> {
        self.authenticate_capability(&port_capability_name(port_id), capability)
    }
}

pub trait PortCapabilityKeeper<M: Into<ModuleId>>:
    PortCapabilityReader<M> + CapabilityKeeper<M>
{
    /// Binds to a port and returns the associated capability
    fn bind_port(
        &mut self,
        port_id: PortId,
    ) -> Result<<Self as CapabilityKeeper<M>>::Capability, Error> {
        if self.is_bound(port_id.clone()) {
            Err(Error::port_already_bound(port_id))
        } else {
            self.new_capability(port_capability_name(port_id))
                .map(Into::into)
        }
    }
}

pub trait CapabilityKeeper<M: Into<ModuleId>> {
    /// The concrete associated `Capability` type
    type Capability: Capability;

    /// The `ModuleId` that this `CapabilityKeeper` is scoped to
    fn module_id(&self) -> M;

    /// Create a new capability with the given name.
    /// Return an error if the capability was already taken.
    fn new_capability(&mut self, name: CapabilityName) -> Result<Self::Capability, Error>;

    /// Claim the specified capability using the specified name.
    /// Return an error if the capability was already taken.
    fn claim_capability(
        &mut self,
        name: CapabilityName,
        capability: Self::Capability,
    ) -> Result<(), Error>;

    /// Release a previously claimed or created capability
    fn release_capability(
        &mut self,
        name: CapabilityName,
        capability: Self::Capability,
    ) -> Result<(), Error>;
}

pub trait CapabilityReader<M: Into<ModuleId>> {
    /// The concrete associated `Capability` type
    type Capability: Capability;

    /// The `ModuleId` that this `CapabilityReader` is scoped to
    fn module_id(&self) -> M;

    /// Find the `ModuleId` that owns this capability
    fn lookup_module(&self, name: &CapabilityName) -> Result<(ModuleId, Self::Capability), Error>;

    /// Fetch a capability which was previously claimed by specified name
    fn get_capability(&self, name: &CapabilityName) -> Result<Self::Capability, Error>;

    /// Authenticate a given capability and name. Lookup the capability from the internal store and
    /// check against the provided name.
    fn authenticate_capability(
        &self,
        name: &CapabilityName,
        capability: &Self::Capability,
    ) -> Result<(), Error>;

    /// Create a new capability with the given name but don't store it.
    fn create_capability(&self, name: CapabilityName) -> Result<Self::Capability, Error>;
}

pub(crate) fn port_capability_name(port_id: PortId) -> CapabilityName {
    PortsPath(port_id)
        .to_string()
        .parse()
        .expect("PortsPath cannot be empty string")
}
