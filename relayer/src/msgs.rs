pub use ibc::events::IBCEvent;
use ibc::ics02_client::client_def::AnyHeader;
pub use tendermint::Signature;

// What is the actual type here?
#[derive(Clone)]
pub enum Datagram {
    NoOp(),
    Packet(Packet),
    ClientUpdate(ClientUpdate),
}

pub type Datagrams = Vec<Datagram>;

#[derive(Clone)]
pub struct Packet {
    // type
// packetData
// seq: number,
// timeout: height,
// timeoutStampt: timestamp,
// commitmentProof: {proof, commitment
}

pub struct Transaction {}

impl Transaction {
    pub fn new(_datagrams: Vec<Datagram>) -> Transaction {
        // calculate the gas
        Self {}
    }

    pub fn sign(self, _signature: Signature) -> SignedTransaction {
        SignedTransaction {}
    }
}

pub struct EncodedTransaction {}

pub struct SignedTransaction {}

impl SignedTransaction {
    pub fn encode(self) -> EncodedTransaction {
        EncodedTransaction {}
    }
}

#[derive(Clone)]
pub struct ClientUpdate {
    signed_headers: Vec<AnyHeader>,
}

impl ClientUpdate {
    pub fn new(signed_headers: Vec<AnyHeader>) -> ClientUpdate {
        ClientUpdate { signed_headers }
    }
}
