use crate::core::ics05_port::error::Error;
use crate::core::ics24_host::identifier::PortId;
use crate::core::ics26_routing::context::ModuleId;
use crate::prelude::*;

/// A context supplying all the necessary read-only dependencies for processing any information regarding a port.
pub trait PortReader {
    /// Return the module_id associated with a given port_id
    fn lookup_module_by_port(&self, port_id: &PortId) -> Result<ModuleId, Error>;
}

pub trait PortKeeper: PortReader {
    /// Binds a module to a port.
    fn bind_module_to_port(&mut self, module_id: ModuleId, port_id: PortId) -> Result<(), Error>;
}
