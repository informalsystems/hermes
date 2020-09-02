use crate::ics02_client::client_def::AnyHeader;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use serde_derive::{Deserialize, Serialize};
use tendermint::block::Height;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockHeader(pub Height);

impl MockHeader {
    pub fn height(&self) -> Height {
        self.0
    }
}

impl From<MockHeader> for AnyHeader {
    fn from(mh: MockHeader) -> Self {
        Self::Mock(mh)
    }
}

impl Header for MockHeader {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }
}
