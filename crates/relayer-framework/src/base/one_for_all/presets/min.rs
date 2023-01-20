use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;
use crate::base::relay::impls::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer;
use crate::base::relay::impls::auto_relayers::concurrent_event::ConcurrentEventSubscriptionRelayer;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;

pub struct MinimalPreset;

pub type ChainStatusQuerier = SendChainStatusQueryToOfa;

pub type ConsensusStateQuerier = SendConsensusStateQueryToOfa;

pub type AutoRelayer = ConcurrentBidirectionalRelayer<ConcurrentEventSubscriptionRelayer>;

pub type PacketRelayer = FullCycleRelayer;

pub type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
