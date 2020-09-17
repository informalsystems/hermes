use crate::types::{ChainId, ChannelId, ClientId, PortId, Datagram};
use crate::connection::{Connection, ConnectionConfig, ConnectionError};
use crate::channel::{Channel, ChannelConfig, ChannelError};
use crate::foreign_client::{ForeignClient, ForeignClientConfig, ForeignClientError};
use crate::chain::{Chain, ChainError, SignedHeader};

pub struct LinkError {}

enum Order {
    Ordered(),
    Unordered(),
}

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
}

impl From<ConnectionError> for LinkError {
    fn from(error: ConnectionError) -> Self {
        return LinkError {}
    }
}

impl From<ChannelError> for LinkError {
    fn from(error: ChannelError ) -> Self {
        return LinkError {}
    }
}

impl From<ForeignClientError> for LinkError {
    fn from(error: ForeignClientError) -> Self {
        return LinkError {}
    }
}

impl From<ChainError> for LinkError {
    fn from(error: ChainError ) -> Self {
        return LinkError {}
    }
}

impl Link {
    // We can probably pass in the connection and channel
    pub fn new(channel: Channel, config: LinkConfig) -> Result<Link, LinkError> {
        // We used to clone these chain objects but if they are traits it's just not possible.

        return Ok(Link {
            src_chain: channel.src_chain,
            dst_chain: channel.dst_chain,
        })
    }

    // Assume subscription returns an iterator of all pending datagrams
    // pre-condition: connection and channel have been established
    // Iterator will error if channel or connection are broken
    fn pending_datagrams(&self) -> Vec<Datagram> {
        return vec![Datagram::NoOp()];
    }

    // Failures
    // * LightClient Failure
    // * FullNode Failures
    // * Verification Failure
    pub fn run(self) -> Result<(), LinkError> {
        let subscription = self.src_chain.subscribe(self.dst_chain.id())?;
        for datagrams in subscription.iter() {
            let target_height = 1; // grab from the datagram
            let header = self.src_chain.get_header(target_height);

            verify_proof(&datagrams, &header);

            self.dst_chain.submit(datagrams); // XXX: Maybe put update_client here
        }

        return Ok(())
    }
}

// XXX: Give this better naming
fn verify_proof(_datagrams: &Vec<Datagram>, _header: &SignedHeader) {
}
