pub type Height = u64;
pub type Hash = ();
pub type Proof = ();
pub type Signature = ();

pub type ChainId = u64;
pub type ClientId = String;
pub type ConnectionId = String;
pub type ChannelId = String;
pub type PortId = String;

pub struct ConsensusState {
    pub height: Height, // Is this superflous?
    pub signed_header: SignedHeader,
}

impl ConsensusState {
    pub fn default() -> ConsensusState {
        return ConsensusState {
            height: 1,
            signed_header: SignedHeader::default(),
        }
    }
}
pub struct SignedHeader {
    pub header: Header,
    pub commit: (),
}

impl SignedHeader {
    pub fn default() -> SignedHeader {
        return SignedHeader {
            header:  Header::default(),
            commit: (),
        }
    }
}

#[derive(std::cmp::PartialEq)]
pub struct Header {
    pub height: Height,
    pub hash: Hash,
    pub app_hash: Hash,
}

pub struct MembershipProof {
    pub height: Height,
}

impl Header {
    pub fn default() -> Header {
        return Header {
            height: 1,
            hash: (),
            app_hash: (),
        }
    }
}
