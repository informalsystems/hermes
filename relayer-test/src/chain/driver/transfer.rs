use ibc::core::ics24_host::identifier::{ChannelId, PortId};

use crate::chain::wallet::WalletAddress;
use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::tagged::*;

use super::ChainDriver;

impl<'a, ChainA> MonoTagged<ChainA, &'a ChainDriver> {
    // We use gaiad instead of the internal raw tx transfer to transfer tokens,
    // as the current chain implementation cannot dynamically switch the sender,
    // and instead always use the configured relayer wallet for sending tokens.
    pub fn transfer_token<ChainB>(
        &self,
        port_id: &DualTagged<ChainA, ChainB, PortId>,
        channel_id: &DualTagged<ChainA, ChainB, ChannelId>,
        sender: &MonoTagged<ChainA, &WalletAddress>,
        receiver: &MonoTagged<ChainB, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<ChainA, &Denom>,
    ) -> Result<(), Error> {
        self.value().exec(&[
            "--node",
            &self.value().rpc_listen_address(),
            "tx",
            "ibc-transfer",
            "transfer",
            port_id.value().as_str(),
            channel_id.value().as_str(),
            &receiver.value().0,
            &format!("{}{}", amount, denom.value().0),
            "--from",
            &sender.value().0,
            "--chain-id",
            self.value().chain_id.as_str(),
            "--home",
            &self.value().home_path,
            "--keyring-backend",
            "test",
            "--yes",
        ])?;

        Ok(())
    }
}
