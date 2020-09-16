use relayer_spike::chain::{ChainRuntime, SignedHeader};
use relayer_spike::link::{Link, LinkConfig};
use relayer_spike::types::Datagram;
use std::thread;

fn main() {
    let config = LinkConfig::default(); // assume this is read from a file 

    // We need:
    let src_chain = ChainRuntime::new(); // TODO: Pass chain config
    let dst_chain = ChainRuntime::new(); // TODO: Pass chain config

    let src_chain_handle = src_chain.handle();
    thread::spawn(move || {
        src_chain.run();
    });

    let dst_chain_handle = dst_chain.handle();
    thread::spawn(move || {
        dst_chain.run();
    });

    match Link::new(src_chain_handle, dst_chain_handle, config) { // TODO: Error Handling
        Ok(link) => {
            link.run();
        },
        // Failures:
        // * Client Failure
        // * Connection Failure
        // * Channel Failure
        Err(err) => panic!("couldn't create a link :("),
    }

    // TODO: Coordinate runtime shutdown
}
