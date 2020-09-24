use relayer_spike::chain::ChainRuntime;
use relayer_spike::foreign_client::{ForeignClient, ForeignClientConfig};
use relayer_spike::connection::{Connection, ConnectionConfig};
use relayer_spike::channel::{Channel, ChannelConfig};
use relayer_spike::link::{Link, LinkConfig};
use std::error::Error;

use std::thread;

fn main() -> Result<(), Box<dyn Error>> {
    let src_chain = ChainRuntime::new(); // TODO: Pass chain config
    let dst_chain = ChainRuntime::new(); // TODO: Pass chain config

    let src_chain_handle = src_chain.handle();
    thread::spawn(move || {
        src_chain.run().unwrap();
    });

    let dst_chain_handle = dst_chain.handle();
    thread::spawn(move || {
        // What should we do on return here?
        dst_chain.run().unwrap();
    });

    // Another idea is to encode the semantic depency more explicitely as
    // foreign_client.new_connect(...).new_channel(...).new_link
    // I think this is actualy what we want
    // Think about how that would work with multiple links

    let foreign_client = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle,
        ForeignClientConfig::default())?;

    let connection = Connection::new(
        &src_chain_handle,
        &dst_chain_handle,
        &foreign_client, // Create a semantic dependecy
        ConnectionConfig::default()).unwrap();

    let channel = Channel::new(
        &src_chain_handle,
        &dst_chain_handle,
        connection, // Semantic dependecy
        ChannelConfig::default()).unwrap();

    let link = Link::new(
        src_chain_handle,
        dst_chain_handle,
        foreign_client, // Actual dependecy
        channel,        // Semantic dependecy
        LinkConfig::default())?;

    link.run()?;

    Ok(())
}
