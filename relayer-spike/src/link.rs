use relayer_spike::{
    Connection, ConnectionError,
    Channel, ChannelError,
}

type ChainId = String;
type ClientId = String;
type ChannelId = String;
type PortId = String;

struct LinkError {}

enum Order {
    Ordered(),
    Unordered(),
}

struct ConfigSide {
    chain_id: ChainId,
    client_id: ClientId,
    channel_id: ChannelId,
    port_id: PortId,
    order: Order,
}

struct Config {
    src_config: ConfigSide,
    dst_config: ConfigSide,
}

struct Link {
    src_chain: Chain,
    dst_chain: Chain,
    connection: Connection,
    channel: Channel,
    port: Port,
}

// TODO: Map between error types

// Here we require chains, connections and channels
impl Link {
    fn new(src: Chain, dest, config: Config) -> Result<Link, LinkError> {
        let connection = Connection::new(src_chain, dest_chain)?;
        let channel = Channel::new(connection, port)?;

        return Link {
            // ... What do we need to keep around
            // We will need the src and dest chain for consutrcting datagrams
        }
    }

    // What if we remove subscription concerns from the link completely and have a higher level
    // concept that subscribes to events from a full node and creates links
    //
    // This will create a stream of events from src_chain destined for dest_chain
    // TODO: Mention in the ADR the case in which events move forward while connection and channels
    // are being established
    fn subscribe(&self) -> Subscription {
        // We first poll for pending_events
        // then we setup the websocket subscription
        // And we prepopulate the subscription with the polled events
        return Subscription {}
    }

    fn pending_datagrams() -> Vec<Datagram> {
        return vec![Datagram{}]
    }

    fn construct_datagrams(event) -> Datagram {
        return Datagram{}
    }
}
