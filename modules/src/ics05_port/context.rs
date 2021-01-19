use crate::ics05_port::capabilities::Capability;
use crate::ics24_host::identifier::PortId;

// A context supplying all the necessary read-only dependencies for processing any information regarding a port.
pub trait PortReader {
    fn lookup_module_by_port(&self, port_id: &PortId) -> Option<Capability>;
    fn autenthenticate(&self, key: &Capability, port_id: &PortId) -> bool;
}

//  Result<Capability, Error>//return Ok(Capability::new());
