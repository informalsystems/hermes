use crate::types::{Height, Hash, ChainId, ChannelId, ClientId, PortId, Datagram};
use crate::connection::ConnectionError;
use crate::channel::{Channel, ChannelError};
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::chain::{Chain, ChainError, SignedHeader, MembershipProof, ConsensusState};
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

    // Failures
    // * LightClient Failure
    // * FullNode Failures
    // * Verification Failure
    pub fn run(mut self) -> Result<(), LinkError> {
        let subscription = self.src_chain.subscribe(self.dst_chain.id())?;
        for datagrams in subscription.iter() {
            // XXX: We do not get full datagrams here, we get events and they need to be converted
            // to datagrams by performing a series of queries on the chains

            let target_height = 1; // grab from the datagram
            let header = self.src_chain.get_header(target_height);

            verify_proof(&datagrams, &header);

            self.foreign_client.update(&*self.src_chain, &*self.dst_chain, target_height)?;
            self.dst_chain.submit(datagrams);
        }

        return Ok(())
    }

}

// XXX: Give this better naming
fn verify_proof(_datagrams: &Vec<Datagram>, _header: &SignedHeader) {
}
