use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, TxBody};

pub struct SignedTx {
    pub body: TxBody,
    pub body_bytes: Vec<u8>,
    pub auth_info: AuthInfo,
    pub auth_info_bytes: Vec<u8>,
    pub signatures: Vec<Vec<u8>>,
}
