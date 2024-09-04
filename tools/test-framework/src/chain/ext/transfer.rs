use core::time::Duration;

use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use crate::chain::chain_type::ChainType;
use crate::chain::cli::transfer::{local_transfer_token, transfer_from_chain};
use crate::chain::driver::ChainDriver;
use crate::chain::tagged::TaggedChainDriverExt;
use crate::error::Error;
use crate::ibc::token::TaggedTokenRef;
use crate::relayer::transfer::{
    batched_ibc_token_transfer, ibc_namada_token_transfer, ibc_token_transfer,
    local_namada_token_transfer,
};
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
        token: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error>;

    fn ibc_transfer_token_with_memo_and_timeout<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        memo: Option<String>,
        timeout: Option<Duration>,
    ) -> Result<(), Error>;

    fn ibc_transfer_token_multiple<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        num_msgs: usize,
        memo: Option<String>,
    ) -> Result<(), Error>;

    fn local_transfer_token(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Chain, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        fees: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error>;

    fn transfer_from_chain<Counterparty>(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        port: &PortId,
        channel: &ChannelId,
        token: &TaggedTokenRef<Chain>,
        fees: &TaggedTokenRef<Chain>,
        timeout_height: &Height,
    ) -> Result<(), Error>;
}

impl<'a, Chain: Send> ChainTransferMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn ibc_transfer_token<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error> {
        match self.value().chain_type {
            crate::chain::chain_type::ChainType::Namada => ibc_namada_token_transfer(
                &self.value().home_path,
                &sender.value().id.to_string(),
                recipient.value().as_str(),
                token.value().denom.as_str(),
                &token.value().amount.to_string(),
                &channel_id.to_string(),
                &self.value().rpc_port.to_string(),
                None,
                None,
            ),
            _ => {
                let rpc_client = self.rpc_client()?;
                self.value().runtime.block_on(ibc_token_transfer(
                    rpc_client.as_ref(),
                    &self.tx_config(),
                    port_id,
                    channel_id,
                    sender,
                    recipient,
                    token,
                    None,
                    None,
                ))
            }
        }
    }

    fn ibc_transfer_token_with_memo_and_timeout<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        memo: Option<String>,
        timeout: Option<Duration>,
    ) -> Result<(), Error> {
        match self.value().chain_type {
            ChainType::Namada => {
                let denom = token.value().denom.to_string();
                let amount = token.value().amount.to_string();
                let rpc_port = self.value().rpc_port.to_string();
                ibc_namada_token_transfer(
                    &self.value().home_path,
                    &sender.value().id.to_string(),
                    recipient.value().as_str(),
                    &denom,
                    &amount,
                    channel_id.value().as_ref(),
                    &rpc_port,
                    memo,
                    timeout,
                )
            }
            _ => {
                let rpc_client = self.rpc_client()?;
                self.value().runtime.block_on(ibc_token_transfer(
                    rpc_client.as_ref(),
                    &self.tx_config(),
                    port_id,
                    channel_id,
                    sender,
                    recipient,
                    token,
                    memo,
                    timeout,
                ))
            }
        }
    }

    fn ibc_transfer_token_multiple<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Chain, Counterparty>,
        channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        num_msgs: usize,
        memo: Option<String>,
    ) -> Result<(), Error> {
        match self.value().chain_type {
            ChainType::Namada => {
                let denom = token.value().denom.to_string();
                let amount = token.value().amount.to_string();
                let rpc_port = self.value().rpc_port.to_string();
                // Namada CLI doesn't support batching transactions
                for _ in 0..num_msgs {
                    ibc_namada_token_transfer(
                        &self.value().home_path,
                        &sender.value().id.to_string(),
                        recipient.value().as_str(),
                        &denom,
                        &amount,
                        &channel_id.to_string(),
                        &rpc_port,
                        memo.clone(),
                        None,
                    )?;
                }
                Ok(())
            }
            _ => {
                let rpc_client = self.rpc_client()?;
                self.value().runtime.block_on(batched_ibc_token_transfer(
                    rpc_client.as_ref(),
                    &self.tx_config(),
                    port_id,
                    channel_id,
                    sender,
                    recipient,
                    token,
                    num_msgs,
                    memo,
                ))
            }
        }
    }

    fn local_transfer_token(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Chain, &WalletAddress>,
        token: &TaggedTokenRef<Chain>,
        fees: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error> {
        let driver = *self.value();
        match driver.chain_type {
            ChainType::Namada => {
                let denom = token.value().denom.to_string();
                let amount = token.value().amount.to_string();
                let rpc_port = self.value().rpc_port.to_string();
                local_namada_token_transfer(
                    &driver.home_path,
                    &sender.value().id.to_string(),
                    recipient.value().as_str(),
                    &denom,
                    &amount,
                    &rpc_port,
                )
            }
            _ => local_transfer_token(
                driver.chain_id.as_str(),
                &driver.command_path,
                &driver.home_path,
                &driver.rpc_listen_address(),
                sender.value().address.as_str(),
                recipient.value().as_str(),
                &token.value().to_string(),
                &fees.value().to_string(),
            ),
        }
    }

    fn transfer_from_chain<Counterparty>(
        &self,
        sender: &MonoTagged<Chain, &Wallet>,
        recipient: &MonoTagged<Counterparty, &WalletAddress>,
        port: &PortId,
        channel: &ChannelId,
        token: &TaggedTokenRef<Chain>,
        fees: &TaggedTokenRef<Chain>,
        timeout_height: &Height,
    ) -> Result<(), Error> {
        let driver = *self.value();
        match driver.chain_type {
            ChainType::Namada => {
                let denom = token.value().denom.to_string();
                let amount = token.value().amount.to_string();
                let rpc_port = self.value().rpc_port.to_string();
                ibc_namada_token_transfer(
                    &driver.home_path,
                    &sender.value().id.to_string(),
                    recipient.value().as_str(),
                    &denom,
                    &amount,
                    channel.as_ref(),
                    &rpc_port,
                    None,
                    None,
                )
            }
            _ => {
                let timeout_height_str = timeout_height.revision_height() + 100;
                transfer_from_chain(
                    driver.chain_id.as_str(),
                    &driver.command_path,
                    &driver.home_path,
                    &driver.rpc_listen_address(),
                    sender.value().address.as_str(),
                    port.as_ref(),
                    channel.as_ref(),
                    recipient.value().as_str(),
                    &token.value().to_string(),
                    &fees.value().to_string(),
                    &timeout_height_str.to_string(),
                )
            }
        }
    }
}
