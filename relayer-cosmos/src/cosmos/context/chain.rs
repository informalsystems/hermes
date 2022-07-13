use async_trait::async_trait;
use core::time::Duration;
use ibc::core::ics04_channel::events::WriteAcknowledgement;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::traits::chain_context::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::core::ErrorContext;
use ibc_relayer_framework::traits::ibc_event_context::IbcEventContext;
use ibc_relayer_framework::traits::sleep::SleepContext;
use tendermint::abci::responses::Event;
use tokio::time::sleep;

use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

#[derive(Clone)]
pub struct CosmosChainContext<Handle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
}

impl<Handle: Async> ErrorContext for CosmosChainContext<Handle> {
    type Error = Error;
}

impl<Handle: Async> ChainContext for CosmosChainContext<Handle> {
    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Event = Event;
}

impl<Chain, Counterparty> IbcChainContext<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type IbcMessage = CosmosIbcMessage;

    type IbcEvent = Event;
}

impl<Chain, Counterparty> IbcEventContext<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type WriteAcknowledgementEvent = WriteAcknowledgement;
}

#[async_trait]
impl<Chain> SleepContext for CosmosChainContext<Chain> {
    async fn sleep(duration: Duration) {
        sleep(duration).await;
    }
}
