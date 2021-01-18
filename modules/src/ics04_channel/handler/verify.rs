use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::context::ChannelReader;

pub fn verify_proofs(
    _ctx: &dyn ChannelReader,
    _channel_end: &ChannelEnd,
    _expected_chan: &ChannelEnd,
) -> bool {
    return true;
}
