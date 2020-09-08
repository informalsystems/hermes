use ibc_proto::tx::v1beta1::{Fee, Tx};

pub struct TxWrapper {
    tx: Tx,
    body: Vec<u8>,
    auth_info: Vec<u8>,

}

trait TxBuilder {
    fn new_builder(msg: Msg) -> Result<StdSignMsg, Error>;
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