use relayer_spike::{Chain, Datagram, SignedHeader};

/*
 * TODO:
 * + Error handling
 * + Spawn multiple paths in a Link abstraction
 */

fn main() {
    // read a config, setup dependencies and launch a link
    // Relay from chain a to chain b

    // Asume that creating such a subscription will create
    
    let config = ...;
    let link = Link::new(config);

    thread::new(move || {
        launch_link(link);
        // TODO: Block on 
    });

}

fn launch_link(link: Link) {&chain_b, 
    // This loop is only for packets
    // TODO: add details to the subscription mechanics and lifecycle management
    for events in link.subscribe() { // this is a blocking subscription
        let target_height = 1;
        // Don't we need to update client on submission
        link.src.update_client(&chain_a, target_height);

        let header = link.src.light_client.get_header(target_height);

        // XXX: Maybe pending_datagrams should be defined on the 
        let datagrams = link.create_datagrams(events);

        // verify that these datagrams are actually part of chain_a
        // Verify that the packet we received from the event was indeed part of chain_a
        verify_proof(&datagrams, &header);

        link.dest.full_node.submit(datagrams); // Maybe put update_client here
    }
}

// XXX: Give this better naming
fn verify_proof(_datagrams: &Vec<Datagram>, _header: &SignedHeader) {
}
