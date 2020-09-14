use crate::types::{ChainId, ChannelId, ClientId, PortId, Datagram};
use crate::connection::{Connection, ConnectionConfig, ConnectionError};
use crate::channel::{Channel, ChannelConfig, ChannelError};
use crate::foreign_client::{ForeignClient, ForeignClientConfig, ForeignClientError};
use crate::chain::{Chain, SignedHeader};

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
    pub src_chain: Chain,
    pub dst_chain: Chain,
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

impl Link {
    // We can probably pass in the connection and channel
    pub fn new(src: Chain, dst: Chain, config: LinkConfig) -> Result<Link, LinkError> {
        // There will probably dependencies between foreign_client, connection and handhsake which
        // will require references to each other..
        let foreign_client = ForeignClient::new(src, dst, ForeignClientConfig::default())?;
        let connection = Connection::new(src, dst, ConnectionConfig::default())?;
        let channel = Channel::new(src, dst, ChannelConfig::default())?;

        return Ok(Link {
            src_chain: src,
            dst_chain: dst,
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
    pub fn run(self) { // TODO: Error
        for datagrams in self.pending_datagrams() { // we batch here to amortize client updates
            let target_height = 1; // grab from the datagram
            let header = self.src_chain.light_client.get_header(target_height);

            verify_proof(&datagrams, &header);

            self.dst_chain.full_node.submit(vec![datagrams]); // Maybe put update_client here
        }
    }
}

// XXX: Give this better naming
fn verify_proof(_datagrams: &Datagram, _header: &SignedHeader) {
}
