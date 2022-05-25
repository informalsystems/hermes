use crate::core::ics02_client::{
    client_type::ClientType,
    header::{AnyHeader, Header},
};

use super::types::LightClientBlockView;

#[derive(Debug, Clone)]
pub struct NearHeader {
    inner: LightClientBlockView,
}

impl NearHeader {
    pub fn get_light_client_block_view(&self) -> &LightClientBlockView {
        &self.inner
    }
}

impl Header for NearHeader {
    fn client_type(&self) -> ClientType {
        ClientType::Near
    }

    fn wrap_any(self) -> AnyHeader {
        AnyHeader::Near(self.inner.clone())
    }
}
