use crate::types::{ChainId, ChannelId, ClientId, PortId};
use crate::msgs::{Datagram, Packet, Transaction, ClientUpdate};
use crate::connection::ConnectionError;
use crate::channel::{Channel, ChannelError};
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::chain::{Chain, ChainError};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("NoOp")]
    NoOp(),

    #[error("Chain error")]
    ChainError(#[from] ChainError),

    #[error("Foreign client error")]
    ForeignClientError(#[from] ForeignClientError),

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),
}

enum Order {
    Ordered(),
    Unordered(),
}

// XXX: There is redundency in the configuration here that can be eliminated by simply passing in
// the dependent objects (ForeignClient, Channel, etc)
// Noting that Links are products of channels
struct ConfigSide {
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
    pub fn default() -> LinkConfig {
        return LinkConfig {
            src_config: ConfigSide {
                port_id: "".to_string(),
                channel_id: "".to_string(),
                chain_id: 0,
                client_id: "".to_string(),
            },
            dst_config: ConfigSide {
                port_id: "".to_string(),
                channel_id: "".to_string(),
                chain_id: 0,
                client_id: "".to_string(),
            },
            order: Order::Unordered(),
        }
    }
}

pub struct Link {
    pub src_chain: Box<dyn Chain>, // XXX: Can these be private?
    pub dst_chain: Box<dyn Chain>,
    foreign_client: ForeignClient,
}

impl Link {
    pub fn new(
        src_chain: impl Chain + 'static,
        dst_chain: impl Chain + 'static,
        foreign_client: ForeignClient,
        _channel: Channel, // We probably need some config here
        _config: LinkConfig) -> Result<Link, LinkError> {

        // XXX: Validate the inputs

        return Ok(Link {
            foreign_client,
            src_chain: Box::new(src_chain),
            dst_chain: Box::new(dst_chain),
        })
    }

    // XXX: We need to export this as a handle function such that it can be unit tested
    // Maybe it should be called CreateTransaction as it maps from events to transactions
    pub fn run(self) -> Result<(), LinkError> {
        let subscription = self.src_chain.subscribe(self.dst_chain.id())?;
        let signature = ();

        // XXX: What about Packet Acks for ordered channels
        for (target_height, events) in subscription.iter() {
            let packets: Result<Vec<Packet>, ChainError> = events.into_iter().map(|event| {
                self.src_chain.create_packet(event)
            }).collect();

            let committed_packets = packets?;

            let mut datagrams: Vec<Datagram> = committed_packets.into_iter().map(|packet| Datagram::Packet(packet)).collect();

            let max_retries = 10; // XXX: move to config
            'submit_retries: for i in 1..max_retries {
                let height = self.dst_chain.get_height(&self.foreign_client)?;
                let signed_headers = self.src_chain.get_minimal_set(height, target_height)?;

                let client_update = ClientUpdate::new(signed_headers);

                datagrams.push(Datagram::ClientUpdate(client_update));

                // We are missing fields here like gas and account
                let transaction = Transaction::new(datagrams.clone());

                let signed_transaction = transaction.sign(signature);

                let encoded_transaction = signed_transaction.encode();
                // How do I know this succeeded?
                match self.dst_chain.submit(encoded_transaction) {
                    Ok(()) => {
                        println!("Submission successful");
                        break 'submit_retries;
                    },
                    Err(err) => {
                        // XXX: We need to determine when the failure is terminal (no more
                        // retries)
                        println!("Submission failed attempt {} with {:?}", i, err);
                    },
                }
            }
        }

        return Ok(())
    }
}
