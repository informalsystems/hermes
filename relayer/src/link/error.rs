use flex_error::define_error;
use ibc::core::ics02_client::error::Error as Ics02Error;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::Height;

use crate::channel::ChannelError;
use crate::connection::ConnectionError;
use crate::error::Error;
use crate::foreign_client::{ForeignClientError, HasExpiredOrFrozenError};
use crate::supervisor::Error as SupervisorError;
use crate::transfer::TransferError;

define_error! {
    LinkError {
        Relayer
            [ Error ]
            |_| { "failed with underlying error" },

        Supervisor
            [ SupervisorError ]
            |_| { "error originating from the supervisor" },

        Initialization
            [ ChannelError ]
            |_| { "link initialization failed during channel counterparty verification" },

        PacketProofsConstructor
            { chain_id: ChainId }
            [ Error ]
            |e| {
                format!("failed to construct packet proofs for chain {0}", e.chain_id)
            },

        Query
            { chain_id: ChainId }
            [ Error ]
            |e| {
                format!("failed during query to chain id {0}", e.chain_id)
            },

        Channel
            [ ChannelError ]
            |_| { "channel error" },

        ChannelNotFound
            {
                port_id: PortId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            [ Error ]
            |e| {
                format!("channel {}/{} does not exist on chain {}",
                    e.port_id, e.channel_id, e.chain_id)
            },

        Connection
            [ ConnectionError ]
            |_| { "connection error" },

        Client
            [ ForeignClientError ]
            |_| { "failed during a client operation" },

        Packet
            [ TransferError ]
            |_| { "packet error" },

        OldPacketClearingFailed
            |_| { "clearing of old packets failed" },

        Send
            { event: IbcEvent }
            |e| {
                format!("chain error when sending messages: {0}", e.event)
            },

        MissingChannelId
            { chain_id: ChainId }
            |e| {
                format!("missing channel_id on chain {}", e.chain_id)
            },

        Signer
            {
                chain_id: ChainId
            }
            [ Error ]
            |e| {
                format!("could not retrieve signer from src chain {}", e.chain_id)
            },

        DecrementHeight
            { height: Height }
            [ Ics02Error ]
            |e| {
                format!("Cannot clear packets @height {}, because this height cannot be decremented", e.height)
            },

        UnexpectedEvent
            { event: IbcEvent }
            |e| {
                format!("unexpected query tx response: {}", e.event)
            },

        InvalidChannelState
            {
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format!("channel {} on chain {} not in open or close state when packets and timeouts can be relayed",
                    e.channel_id, e.chain_id)
            },

        ChannelNotOpened
            {
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format!("connection for channel {} on chain {} is not in open state",
                    e.channel_id, e.chain_id)
            },

        CounterpartyChannelNotFound
            {
                channel_id: ChannelId,
            }
            |e| {
                format!("counterparty channel id not found for {}",
                    e.channel_id)
            },

        NoConnectionHop
            {
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format!("channel {} on chain {} has no connection hops",
                    e.channel_id, e.chain_id)
            },

        UpdateClientFailed
             |_| { "failed to update client" },
   }
}

impl HasExpiredOrFrozenError for LinkErrorDetail {
    fn is_expired_or_frozen_error(&self) -> bool {
        match self {
            Self::Client(e) => e.source.is_expired_or_frozen_error(),
            _ => false,
        }
    }
}

impl HasExpiredOrFrozenError for LinkError {
    fn is_expired_or_frozen_error(&self) -> bool {
        self.detail().is_expired_or_frozen_error()
    }
}
