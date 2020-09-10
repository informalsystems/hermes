use ibc_proto::tx::v1beta1::{Tx, TxBody, AuthInfo};
use ibc::tx_msg::Msg;
use crate::error::Error;

pub struct TxWrapper {
    tx: Tx,
    body: Vec<u8>,
    auth_info: Vec<u8>,

}

pub struct TxBuilder {

}

impl TxBuilder {
    pub fn new_builder<T: std::error::Error, U: Msg<ValidationError = T>>(msg: Vec<Box<U>>, memo: String, height: u64) -> Result<(), Error> {
        // let mut proto_msgs: Vec<prost_types::Any> = Vec::new();
        // let mut buf = Vec::new();
        //
        // // Have a loop if new_builder takes more messages
        // // for now just encode one message
        // prost::Message::encode(&msg, &mut buf).unwrap();
        //
        // // Create a proto any message
        // let any_msg = prost_types::Any {
        //     type_url: "type.googleapis.com/ibc.messages.MsgConnectionOpenInit".to_string(),
        //     value: buf,
        // };
        //
        // // Add proto message
        // proto_msgs.push(any_msg);
        //
        // // Create TxBody
        // let body = TxBody {
        //     messages: proto_msgs,
        //     memo,
        //     timeout_height: height,
        //     extension_options: Vec::<prost_types::Any>::new(),
        //     non_critical_extension_options: Vec::<prost_types::Any>::new(),
        // };
        //
        // let auth_info = AuthInfo {
        //
        // };
        unimplemented!()
    }
}

// pub struct StdSignMsg {
//     chain_id: ChainId,
//     account: AccountId,
//     timeout_height: Height,
//     msgs: Vec<dyn Msg>,
//     memo: String,
//     fee: Fee,
//     sequence: Sequence
// }