use relayer_spike::chain::{Chain, SignedHeader};
use relayer_spike::link::{Link, LinkConfig};
use relayer_spike::types::Datagram;


fn main() {
    let config = LinkConfig::default(); // assume this is read from a file 

    let src_chain = Chain::new(); // TODO: Pass chain config
    let dst_chain = Chain::new();  // TODO: Pass chain config

    // TODO: Run the chain runtimes

    match Link::new(src_chain, dst_chain, config) { // TODO: Error Handling
        Ok(link) => {
            link.run();
        },
        // Failures:
        // * Client Failure
        // * Connection Failure
        // * Channel Failure
        Err(err) => panic!("couldn't create a link :("),
    }
}
