use ibc_relayer_components::relay::impls::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer;
use ibc_relayer_components::relay::impls::auto_relayers::concurrent_event::ConcurrentEventSubscriptionRelayer;
use ibc_relayer_components::relay::impls::auto_relayers::concurrent_two_way::ConcurrentTwoWayAutoRelay;
use ibc_relayer_components::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::impls::packet_filters::allow_all::AllowAll;
use ibc_relayer_components::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;

use crate::base::one_for_all::impls::chain::queries::consensus_state::SendConsensusStateQueryToOfa;
use crate::base::one_for_all::impls::chain::queries::status::SendChainStatusQueryToOfa;

pub struct MinimalPreset;

pub type ChainStatusQuerier = SendChainStatusQueryToOfa;

pub type ConsensusStateQuerier = SendConsensusStateQueryToOfa;

pub type AutoRelayer = ConcurrentBidirectionalRelayer<ConcurrentEventSubscriptionRelayer>;

pub type PacketRelayer = FullCycleRelayer;

pub type PacketFilter = AllowAll;

pub type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;

pub type TwoWayAutoRelayer = ConcurrentTwoWayAutoRelay;
