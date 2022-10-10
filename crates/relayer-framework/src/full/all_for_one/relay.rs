use crate::base::all_for_one::traits::relay::AfoRelayContext;
use crate::full::filter::traits::filter::HasPacketFilter;

pub trait AfoFullRelayContext: AfoRelayContext + HasPacketFilter {}

impl<Relay> AfoFullRelayContext for Relay where Relay: AfoRelayContext + HasPacketFilter {}
