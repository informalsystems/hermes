use relayer_spike::{Chain, Datagram, SignedHeader};

/*
 * TODO:
 * + Error handling
 * + Spawn multiple paths in a Relay abstraction
 */

fn main() {
    // Relay from chain a to chain b
    let mut chain_a = Chain::new();
    let mut chain_b = Chain::new();

    // Asume that creating such a subscription will create
    let mut subscription =  chain_a.full_node.subscribe();

    for event in subscription.iter() {
        let target_height = 1;
        // XXX: Do we want to bundle client update datagrams with packets?
        // A: This can be asynchronous to client to packet creation
        // B: Confirming packet submission requires and up to date client
        chain_b.update_client(&chain_a, target_height);

        let header = chain_a.light_client.get_header(target_height);

        // What other datagrams are we sending here besides those produced from the event?
        // we can assume that this
        let datagrams = chain_a.full_node.pending_datagrams(&chain_b, event); // s/pending_datagrams/create_packet

        // verify that these datagrams are actually part of chain_a
        // Verify that the packet we received from the event was indeed part of chain_a
        verify_proof(&datagrams, &header);

        chain_b.full_node.submit(datagrams); // Maybe put update_client here
    }
}

fn verify_proof(_datagrams: &Vec<Datagram>, _header: &SignedHeader) {
}
