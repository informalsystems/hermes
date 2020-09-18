use relayer_spike::chain::ChainRuntime;
use relayer_spike::foreign_client::{ForeignClient, ForeignClientConfig};
use relayer_spike::connection::{Connection, ConnectionConfig};
use relayer_spike::channel::{Channel, ChannelConfig};
use relayer_spike::link::{Link, LinkConfig};

use std::thread;

fn main() {
    let src_chain = ChainRuntime::new(); // TODO: Pass chain config
    let dst_chain = ChainRuntime::new(); // TODO: Pass chain config

    let src_chain_handle = src_chain.handle();
    thread::spawn(move || {
        src_chain.run().unwrap();
    });

    let dst_chain_handle = dst_chain.handle();
    thread::spawn(move || {
        dst_chain.run().unwrap();
    });

    let foreign_client = ForeignClient::new(src_chain_handle, dst_chain_handle, ForeignClientConfig::default()).unwrap();
    let connection = Connection::new(foreign_client, ConnectionConfig::default()).unwrap();
    let channel = Channel::new(connection, ChannelConfig::default()).unwrap();

    // What if we create the clients and stuff here and then pass the link
    match Link::new(channel, LinkConfig::default()) { // TODO: Error Handling
        Ok(link) => {
            link.run().unwrap();
        },
        // Failures:
        // * Client Failure
        // * Connection Failure
        // * Channel Failure
        Err(_err) => panic!("couldn't create a link :("),
    }
}
