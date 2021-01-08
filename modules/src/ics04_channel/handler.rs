//! This module implements the processing logic for ICS4 (channel) messages.

use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::Error;
use crate::ics04_channel::msgs::ChannelMsg;
use crate::ics05_port::capabilities::Capability;
use crate::ics24_host::identifier::{ChannelId, PortId};

pub mod chan_open_init;

#[derive(Clone, Debug)]
pub enum ChannelEvent {
    ChanOpenInit(ChannelResult),
    // ConnOpenTry(ConnectionResult),
    // ConnOpenAck(ConnectionResult),
    // ConnOpenConfirm(ConnectionResult),
}

#[derive(Clone, Debug)]
pub struct ChannelResult {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub channel_cap: Capability,
    pub channel_end: ChannelEnd,
}

impl From<ChannelEvent> for Event {
    fn from(ev: ChannelEvent) -> Event {
        match ev {
            ChannelEvent::ChanOpenInit(_chan) => Event::new(
                EventType::Custom("channel_open_init".to_string()),
                vec![("channel_id".to_string(), "None".to_string())],
            ),
            // ChannelEvent::ChanOpenTry(conn) => Event::new(
            //     EventType::Custom("channel_open_try".to_string()),
            //     vec![("channel_id".to_string(), chan.channel_id.to_string())],
            // ),
            // ChannelEvent::ChanOpenAck(conn) => Event::new(
            //     EventType::Custom("channel_open_ack".to_string()),
            //     vec![("channel_id".to_string(), chan.channel_id.to_string())],
            // ),
            // ChannelEvent::ChanOpenConfirm(conn) => Event::new(
            //     EventType::Custom("channel_open_confirm".to_string()),
            //     vec![("channel_id".to_string(), conn.channel _id.to_string())],
            // ),
        }
    }
}

/// General entry point for processing any type of message related to the ICS4 channel open
/// handshake protocol.
pub fn dispatch<Ctx>(ctx: &Ctx, msg: ChannelMsg) -> Result<HandlerOutput<ChannelResult>, Error>
where
    Ctx: ChannelReader,
{
    Ok(match msg {
        ChannelMsg::ChannelOpenInit(msg) => chan_open_init::process(ctx, msg)?,
        // ChannelMsg::ChannelOpenTry(msg) => chan_open_try::process(ctx, *msg)?,
        // ChannelMsg::ChannelOpenAck(msg) => chan_open_ack::process(ctx, *msg)?,
        // ChannelMsg::ChannelOpenConfirm(msg) => chan_open_confirm::process(ctx, msg)?,
        _ => panic!(),
    })
}
