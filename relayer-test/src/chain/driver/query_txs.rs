use serde_json as json;

use crate::chain::wallet::WalletAddress;
use crate::error::Error;
use crate::tagged::*;

use super::ChainDriver;

impl<'a, ChainA> MonoTagged<ChainA, &'a ChainDriver> {
    pub fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<ChainA, &WalletAddress>,
    ) -> Result<json::Value, Error> {
        let res = self.value().exec(&[
            "--node",
            &self.value().rpc_listen_address(),
            "query",
            "txs",
            "--events",
            &format!("transfer.recipient={}", recipient_address.value().0),
        ])?;

        let json_res = json::from_str(&res)?;

        Ok(json_res)
    }
}
