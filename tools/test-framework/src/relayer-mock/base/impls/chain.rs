use crate::base::error::Error;

impl<Chain> OfaChainTypes for MockChainWrapper<Chain>
where
    Chain: MockChain,
{
    type Preset = ;

    type Error = Error;

    type Runtime = ;

    type Height = u128;

    type Timestamp = ;

    type Message = String;

    type Signer = ;

    type RawMessage = Vec<u8>;

    type Event = ;

    type ClientId = String;

    type ConnectionId = String;

    type ChannelId = String;

    type PortId = String;

    type Sequence = u128;

    type WriteAcknowledgementEvent = ;

    type ConsensusState = ;

    type ChainStatus = ;
}