use std::ops::Range;

use crate::chain::handle::{ChainHandle, ChainHandleError};
use crate::chain::{Chain, CosmosSDKChain};
use crate::channel::{Channel, ChannelError};
use crate::connection::ConnectionError;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::msgs::{ClientUpdate, Datagram, Packet, Transaction};
use ibc::{
    ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId},
    Height,
};
use retry::{delay::Fixed, retry, Error as RetryError};
use tendermint::Signature;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("Failed")]
    Failed,

    #[error("Chain handle error")]
    ChainError(#[from] ChainHandleError),

    #[error("Foreign client error")]
    ForeignClientError(#[from] ForeignClientError),

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),

    #[error("RetryExhausted:")]
    RetryError(#[from] RetryError<ChainHandleError>),
}

pub enum Order {
    Ordered,
    Unordered,
}

// XXX: There is redundency in the configuration here that can be eliminated by simply passing in
// the dependent objects (ForeignClient, Channel, etc)
// Noting that Links are products of channels
pub struct ConfigSide {
    chain_id: ChainId,
    client_id: ClientId,
    channel_id: ChannelId,
    port_id: PortId,
}

pub struct LinkConfig {
    src_config: ConfigSide,
    dst_config: ConfigSide,
    order: Order,
}

impl LinkConfig {
    pub fn new(src_config: ConfigSide, dst_config: ConfigSide, order: Order) -> LinkConfig {
        Self {
            src_config,
            dst_config,
            order,
        }
    }
}

pub struct Link {
    src_chain: Box<dyn ChainHandle>,
    dst_chain: Box<dyn ChainHandle>,
    foreign_client: ForeignClient,
}

impl Link {
    pub fn new(
        src_chain: impl ChainHandle + 'static,
        dst_chain: impl ChainHandle + 'static,
        foreign_client: ForeignClient,
        _channel: Channel, // We probably need some config here
        _config: LinkConfig,
    ) -> Result<Link, LinkError> {
        // XXX: Validate the inputs

        Ok(Link {
            foreign_client,
            src_chain: Box::new(src_chain),
            dst_chain: Box::new(dst_chain),
        })
    }

    pub fn run(self) -> Result<(), LinkError> {
        // XXX: subscriptions are per channel
        // Subscriptions have to buffer events as packets can be sent before channels are
        // established
        // Can subscriptions operate as queues?
        let subscription = self.src_chain.subscribe(self.dst_chain.id())?;
        let signature = todo!();

        // XXX: What about Packet Acks for ordered channels
        for (target_height, events) in subscription.iter() {
            let packets: Result<Vec<_>, _> = events
                .into_iter()
                .map(|event| self.src_chain.create_packet(event))
                .collect();

            let committed_packets = packets?;

            let datagrams = committed_packets
                .into_iter()
                .map(Datagram::Packet)
                .collect::<Vec<_>>();

            let max_retries = 10_usize; // XXX: move to config
            let mut tries = 0..max_retries;

            let result = retry(Fixed::from_millis(100), || {
                if let Some(attempt) = tries.next() {
                    self.step(target_height, datagrams.clone(), signature)
                } else {
                    Err(ChainHandleError::Failed)
                }
            });

            match result {
                Ok(_) => {
                    println!("Submission successful");
                    Ok(())
                }
                Err(problem) => {
                    println!("Submission failed attempt with {:?}", problem);
                    Err(LinkError::Failed)
                }
            }?;
        }

        Ok(())
    }

    fn step(
        &self,
        target_height: Height,
        mut datagrams: Vec<Datagram>,
        signature: Signature,
    ) -> Result<(), ChainHandleError> {
        let height = self.dst_chain.get_height(&self.foreign_client)?;
        // XXX: Check that height > target_height, no client update needed
        let signed_headers = self.src_chain.get_minimal_set(height, target_height)?;

        let client_update = ClientUpdate::new(signed_headers);

        datagrams.push(Datagram::ClientUpdate(client_update));

        // We are missing fields here like gas and account
        let transaction = Transaction::new(datagrams);
        let signed_transaction = transaction.sign(signature);
        let encoded_transaction = signed_transaction.encode();

        // Submission failure cases
        // - The full node can fail
        //  + TODO: The link will fail, and signale recreation with a different full node
        // - The transaction can be rejected because the client is not up to date
        //  + Retry this loop
        self.dst_chain.submit(encoded_transaction)?;

        Ok(())
    }
}
