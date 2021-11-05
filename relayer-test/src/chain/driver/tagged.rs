use serde_json as json;

use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::types::id::{ChannelId, PortId};
use crate::types::tagged::*;
use crate::types::wallet::{Wallet, WalletAddress};

use super::query_txs::query_recipient_transactions;
use super::transfer::transfer_token;
use super::ChainDriver;

pub trait TaggedChainDriver<Chain> {
    fn query_balance(
        &self,
        wallet_id: &MonoTagged<Chain, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<u64, Error>;

    fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<Chain, &Wallet>,
        target_amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error>;

    fn transfer_token<Counterparty>(
        &self,
        port_id: &PortId<Chain, Counterparty>,
        channel_id: &ChannelId<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &WalletAddress>,
        receiver: &MonoTagged<Counterparty, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error>;

    fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<Chain, &WalletAddress>,
    ) -> Result<json::Value, Error>;
}

impl<'a, Chain> TaggedChainDriver<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn query_balance(
        &self,
        wallet_id: &MonoTagged<Chain, &WalletAddress>,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<u64, Error> {
        self.value().query_balance(wallet_id.value(), denom.value())
    }

    fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<Chain, &Wallet>,
        target_amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error> {
        self.value()
            .assert_eventual_wallet_amount(user.value(), target_amount, denom.value())
    }

    fn transfer_token<Counterparty>(
        &self,
        port_id: &PortId<Chain, Counterparty>,
        channel_id: &ChannelId<Chain, Counterparty>,
        sender: &MonoTagged<Chain, &WalletAddress>,
        receiver: &MonoTagged<Counterparty, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<Chain, &Denom>,
    ) -> Result<(), Error> {
        transfer_token(
            self.value(),
            port_id.value(),
            channel_id.value(),
            sender.value(),
            receiver.value(),
            amount,
            denom.value(),
        )
    }

    fn query_recipient_transactions(
        &self,
        recipient_address: &MonoTagged<Chain, &WalletAddress>,
    ) -> Result<json::Value, Error> {
        query_recipient_transactions(self.value(), recipient_address.value())
    }
}
