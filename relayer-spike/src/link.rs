use crate::types::{ChainId, ChannelId, ClientId, PortId};
use crate::msgs::{Datagram, Packet, Transaction, ClientUpdate};
use crate::connection::ConnectionError;
use crate::channel::{Channel, ChannelError};
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::chain::{Chain, ChainError};
use thiserror::Error;
use retry::{retry, Error as RetryError, delay::Fixed};

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("Failed")]
    Failed(),

    #[error("Chain error")]
    ChainError(#[from] ChainError),

    #[error("Foreign client error")]
    ForeignClientError(#[from] ForeignClientError),

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),

    #[error("RetryExhausted:")]
    RetryError(#[from] RetryError<ChainError>),
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

    // How can we refactor this to enable testing
    // What we need is for the 

    pub fn run(self) -> Result<(), LinkError> {
        let subscription = self.src_chain.subscribe(self.dst_chain.id())?;
        let signature = ();

        // XXX: What about Packet Acks for ordered channels
        for (target_height, events) in subscription.iter() {
            let packets: Result<Vec<Packet>, ChainError> = events.into_iter().map(|event| {
                self.src_chain.create_packet(event)
            }).collect();

            let committed_packets = packets?;

            let datagrams: Vec<Datagram> = committed_packets.into_iter().map(|packet| Datagram::Packet(packet)).collect();

            let max_retries = 10; // XXX: move to config
            let mut tries = 0..max_retries;
            let result = retry(Fixed::from_millis(100), || -> Result<(), ChainError> {
                if let Some(attempt) = tries.next() {
                    let height = self.dst_chain.get_height(&self.foreign_client)?;
                    let signed_headers = self.src_chain.get_minimal_set(height, target_height)?;

                    let client_update = ClientUpdate::new(signed_headers);
                    let mut attempt_datagrams = datagrams.clone();

                    attempt_datagrams.push(Datagram::ClientUpdate(client_update));

                    // We are missing fields here like gas and account
                    let transaction = Transaction::new(attempt_datagrams);

                    let signed_transaction = transaction.sign(signature);

                    let encoded_transaction = signed_transaction.encode();
                    self.dst_chain.submit(encoded_transaction)?
                } else {
                    Err::<(), ChainError>(ChainError::Failed());
                }

                return Ok(())
            });

            match result {
                Ok(_) => {
                    println!("Submission successful");
                },
                Err(problem) => {
                    println!("Submission failed attempt with {:?}", problem);
                    return Err(LinkError::Failed());
                }
            }
        }

        return Ok(())
    }
}
