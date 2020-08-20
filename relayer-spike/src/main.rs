use relayer_spike::chain::{Chain, SignedHeader};
use relayer_spike::link::{Link, LinkConfig};
use relayer_spike::types::Datagram;


fn main() {
    let config = LinkConfig::default(); // assume this is read from a file 
    
    let src_chain =  Chain::new();
    let dst_chain = Chain::new();
    match Link::new(src_chain, dst_chain, config) {
        Ok(link) => {
            launch_link(link);
        },
        Err(err) => panic!("couldn't create a link :("),
    }
}

// TODO: Think about failure here
// Full node could fail here
// This link API might be simpler here
// perhaps it's just:
// link.verify_datagrams
// link.submit_datagrams
fn launch_link(link: Link) {
    for datagrams in link.pending_datagrams() { // we batch here to amortize client updates
        let target_height = 1; // grab from the datagram
        let header = link.src_chain.light_client.get_header(target_height);

        verify_proof(&datagrams, &header);

        link.dst_chain.full_node.submit(vec![datagrams]); // Maybe put update_client here
    }
}

// XXX: Give this better naming
fn verify_proof(_datagrams: &Datagram, _header: &SignedHeader) {
}
