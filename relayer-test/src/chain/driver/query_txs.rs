use serde_json as json;

use crate::error::Error;
use crate::types::tagged::*;
use crate::types::wallet::WalletAddress;

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

        // tracing::debug!("parsing tx result: {}", res);

        let json_res = json::from_str(&res)?;

        Ok(json_res)
    }
}
