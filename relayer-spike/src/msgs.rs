use crate::types::{Signature, SignedHeader};

// What is the actual type here?
pub enum Datagram {
    NoOp(),
    Packet(Packet),
    ClientUpdate(ClientUpdate),
}

pub struct Packet {
    // type
    // packetData
    // seq: number,
    // timeout: height,
    // timeoutStampt: timestamp,
    // commitmentProof: {proof, commitment
}

pub struct Transaction {
}

impl Transaction {
    pub fn new(datagrams: Vec<Datagram>) -> Transaction {
        // calculate the gas
        return Transaction {}
    }

    pub fn sign(self, signature: Signature) -> SignedTransaction {
        return SignedTransaction {}
    }
}

pub struct EncodedTransaction {
}

pub struct SignedTransaction {
}

impl SignedTransaction {
    pub fn encode(self) -> EncodedTransaction {
        return EncodedTransaction {}
    }
}


// XXX: Replace with ibc-rs::modules::events::IBCEvent
pub enum IBCEvent {
    NoOp(),
}

pub struct ClientUpdate {
    signed_headers: Vec<SignedHeader>,
}

impl ClientUpdate {
    pub fn new(signed_headers: Vec<SignedHeader>) -> ClientUpdate {
        return ClientUpdate {
            signed_headers,
        }
    }
}
