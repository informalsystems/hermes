use core::time::Duration;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::chain::cli::transfer::local_transfer_token;
use crate::chain::driver::ChainDriver;
use crate::chain::tagged::TaggedChainDriverExt;
use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::relayer::transfer::ibc_token_transfer;
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::*;
use crate::types::wallet::{Wallet, WalletAddress};

pub trait ChainTransferMethodsExt<Chain> {
    /**
       Submits an IBC token transfer transaction to `Chain` to any other
       `Counterparty` chain.

       The following parameters are accepted:

       - A `PortId` on `Chain` that corresponds to a channel connected to
         `Counterparty`.

       - A `ChannelId` on `Chain` that corresponds to a channel connected to
         `Counterparty`.

       - The [`Wallet`] of the sender on `Chain`.

       - The [`WalletAddress`] address of the recipient on `Counterparty`.

       - The denomination of the amount on `Chain`.

       - The transfer amount.
    */
    fn ibc_transfer_token<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
        amount: u64,
        timeout: Option<Duration>,
    ) -> Result<Packet, Error>;

    fn local_transfer_token(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Chain, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error>;
}

impl<'a, Chain: Send> ChainTransferMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn ibc_transfer_token<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
        amount: u64,
        timeout: Option<Duration>,
    ) -> Result<Packet, Error> {
        self.value().runtime.block_on(ibc_token_transfer(
            &self.tx_config(),
            port_id,
            channel_id,
            sender,
            recipient,
            denom,
            amount,
            timeout,
        ))
    }

    fn local_transfer_token(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Chain, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error> {
        let driver = *self.value();
        local_transfer_token(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            sender.value().address.as_str(),
            recipient.value().as_str(),
            &format!("{}{}", amount, denom),
        )
    }
}
