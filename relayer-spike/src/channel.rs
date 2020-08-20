struct ChannelError {
}

struct ChannelConfig {
    chain_id: ChainId,
    client_id: ClientId,
}

struct Channel {
}

impl Channel {
    // we need ChannelConfig
    // * chain_id
    // * client_id
    // * channel_id
    // * connection_id
    // * port_id
    // * order
    fn new(src_chain: Chain, dest_chain, ChannelConfig) -> Result<Channel, ChannelError> {
        // perform channel handshake
        return Ok(Channel{})
    }
}
