use crate::core::ics02_client::header::Header;

#[derive(Debug, Clone)]
pub struct NearHeader {}

impl Header for NearHeader {
    fn client_type(&self) -> crate::core::ics02_client::client_type::ClientType {
        todo!()
    }

    fn wrap_any(self) -> crate::core::ics02_client::header::AnyHeader {
        todo!()
    }
}
