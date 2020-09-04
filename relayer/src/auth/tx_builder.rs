use ibc_proto::tx::v1beta1::{Fee, Tx};

pub struct TxWrapper {
    tx: Tx
}

trait TxBuilder {
    fn new_builder();
}

pub struct StdSignMsg {
    chain_id: ChainId,
    account: AccountId,
    timeout_height: Height,
    msgs: Vec<dyn Msg>,
    memo: String,
    fee: Fee,
    sequence: Sequence
}
//
// let msgs = vec![];
// // let any: //TODO How self can be 'Any'
// let raw = TxRaw {
// body_bytes: vec![],
// auth_info_bytes: vec![],
// signatures: vec![]
// };
// let body = TxBody {
// messages: vec![self.as_any().],
// memo: TYPE_MSG_CONNECTION_OPEN_INIT.to_string(),
// timeout_height: 0,
// extension_options: vec![],
// non_critical_extension_options: vec![]
// };
//
//
// // let doc = SignDoc {
// //     bodyBytes: body..length > 0 ? body : null, // normalize empty bytes to unset
// //     authInfoBytes: authInfo.length > 0 ? authInfo : null, // normalize empty bytes to unset
// //     chainId: chainId || null, // normalize "" to unset
// //     accountNumber: accountNumber || null, // normalize 0 to unset
// //     accountSequence: accountSequence || null, // normalize 0 to unset
// // }).finish();