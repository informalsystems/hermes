use std::fmt;
use std::time::Instant;

use prost_types::Any;
use tracing::{info, warn};

use ibc::events::IbcEvent;
use ibc::tagged::Tagged;
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::link::error::LinkError;
use crate::link::RelayPath;

#[derive(Clone, Copy, PartialEq)]
pub enum OperationalDataTarget {
    Source,
    Destination,
}

impl fmt::Display for OperationalDataTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationalDataTarget::Source => write!(f, "Source"),
            OperationalDataTarget::Destination => write!(f, "Destination"),
        }
    }
}

/// A packet messages that is prepared for sending to a chain, but has not been sent yet.
/// Comprises both the proto-encoded packet message, alongside the event which generated it.
#[derive(Clone)]
pub struct TransitMessage<Chain> {
    pub event: Tagged<Chain, IbcEvent>,
    pub msg: Tagged<Chain, Any>,
}

/// Holds all the necessary information for handling a set of in-transit messages.
///
/// Each `OperationalData` item is uniquely identified by the combination of two attributes:
///     - `target`: represents the target of the packet messages, either source or destination chain,
///     - `proofs_height`: represents the height for the proofs in all the messages.
///       Note: this is the height at which the proofs are queried. A client consensus state at
///       `proofs_height + 1` must exist on-chain in order to verify the proofs.
#[derive(Clone)]
pub enum OperationalData<SrcChain, DstChain> {
    Src(SrcOperationPayload<SrcChain, DstChain>),
    Dst(DstOperationPayload<SrcChain, DstChain>),
}

pub enum AssembledMessages<SrcChain, DstChain> {
    Src(Vec<Tagged<SrcChain, Any>>),
    Dst(Vec<Tagged<DstChain, Any>>),
}

#[derive(Clone)]
pub struct OperationPayload<Chain, Counterparty> {
    pub proofs_height: Tagged<Counterparty, Height>,
    pub batch: Vec<TransitMessage<Chain>>,
    /// Stores the time when the clients on the target chain has been updated, i.e., when this data
    /// was scheduled. Necessary for packet delays.
    pub scheduled_time: Instant,
}

#[derive(Clone)]
pub struct SrcOperationPayload<SrcChain, DstChain> {
    pub proofs_height: Tagged<DstChain, Height>,
    pub batch: Vec<(Tagged<SrcChain, IbcEvent>, Tagged<SrcChain, Any>)>,
    /// Stores the time when the clients on the target chain has been updated, i.e., when this data
    /// was scheduled. Necessary for packet delays.
    pub scheduled_time: Instant,
}

#[derive(Clone)]
pub struct DstOperationPayload<SrcChain, DstChain> {
    pub proofs_height: Tagged<SrcChain, Height>,
    pub batch: Vec<(Tagged<SrcChain, IbcEvent>, Tagged<DstChain, Any>)>,
    /// Stores the time when the clients on the target chain has been updated, i.e., when this data
    /// was scheduled. Necessary for packet delays.
    pub scheduled_time: Instant,
}

impl<SrcChain, DstChain> SrcOperationPayload<SrcChain, DstChain> {
    pub fn new(proofs_height: Tagged<DstChain, Height>) -> Self {
        SrcOperationPayload {
            proofs_height,
            batch: vec![],
            scheduled_time: Instant::now(),
        }
    }

    pub fn batch_events(&self) -> Vec<Tagged<SrcChain, IbcEvent>> {
        self.batch.iter().map(|(event, _)| event.clone()).collect()
    }

    pub fn batch_messages(&self) -> Vec<Tagged<SrcChain, Any>> {
        self.batch.iter().map(|(_, msg)| msg.clone()).collect()
    }
}

impl<SrcChain, DstChain> DstOperationPayload<SrcChain, DstChain> {
    pub fn new(proofs_height: Tagged<SrcChain, Height>) -> Self {
        DstOperationPayload {
            proofs_height,
            batch: vec![],
            scheduled_time: Instant::now(),
        }
    }

    pub fn batch_events(&self) -> Vec<Tagged<SrcChain, IbcEvent>> {
        self.batch.iter().map(|(event, _)| event.clone()).collect()
    }

    pub fn batch_messages(&self) -> Vec<Tagged<DstChain, Any>> {
        self.batch.iter().map(|(_, msg)| msg.clone()).collect()
    }
}

impl<Chain, Counterparty> OperationPayload<Chain, Counterparty> {
    pub fn new(proofs_height: Tagged<Counterparty, Height>) -> Self {
        OperationPayload {
            proofs_height,
            batch: vec![],
            scheduled_time: Instant::now(),
        }
    }

    pub fn batch_events(&self) -> Vec<Tagged<Chain, IbcEvent>> {
        self.batch.iter().map(|gm| gm.event).collect()
    }

    pub fn batch_messages(&self) -> Vec<Tagged<Chain, Any>> {
        self.batch.iter().map(|gm| gm.msg).collect()
    }
}

impl<Chain> TransitMessage<Chain> {
    pub fn new(event: Tagged<Chain, IbcEvent>, msg: Tagged<Chain, Any>) -> Self {
        Self { event, msg }
    }
}

impl<SrcChain, DstChain> AssembledMessages<SrcChain, DstChain> {
    pub fn len(&self) -> usize {
        match self {
            Self::Src(messages) => messages.len(),
            Self::Dst(messages) => messages.len(),
        }
    }
}

impl<SrcChain, DstChain> OperationalData<SrcChain, DstChain> {
    pub fn new_src(proofs_height: Tagged<DstChain, Height>) -> Self {
        OperationalData::Src(SrcOperationPayload::new(proofs_height))
    }

    pub fn new_dst(proofs_height: Tagged<SrcChain, Height>) -> Self {
        OperationalData::Dst(DstOperationPayload::new(proofs_height))
    }

    pub fn target(&self) -> OperationalDataTarget {
        match self {
            Self::Src(_) => OperationalDataTarget::Source,
            Self::Dst(_) => OperationalDataTarget::Destination,
        }
    }

    pub fn batch_len(&self) -> usize {
        match self {
            Self::Src(data) => data.batch.len(),
            Self::Dst(data) => data.batch.len(),
        }
    }

    pub fn is_empty_batch(&self) -> bool {
        match self {
            Self::Src(data) => data.batch.is_empty(),
            Self::Dst(data) => data.batch.is_empty(),
        }
    }
}

impl<SrcChain, DstChain> OperationalData<SrcChain, DstChain>
where
    SrcChain: ChainHandle<DstChain>,
    DstChain: ChainHandle<SrcChain>,
{
    /// Returns all the messages in this operational data, plus prepending the client update message
    /// if necessary.
    pub fn assemble_msgs(
        &self,
        relay_path: &RelayPath<SrcChain, DstChain>,
    ) -> Result<AssembledMessages<SrcChain, DstChain>, LinkError> {
        let messages = match self {
            Self::Src(data) => {
                let mut batch_messages = data.batch_messages();

                if batch_messages.is_empty() {
                    warn!("assemble_msgs() method call on an empty OperationalData!");
                    return Ok(AssembledMessages::Src(batch_messages));
                }

                // For zero delay we prepend the client update msgs.
                if relay_path.zero_delay() {
                    let update_height = data.proofs_height.map(|h| h.increment());

                    info!(
                        "[{}] prepending {} client update @ height {}",
                        relay_path,
                        self.target(),
                        update_height
                    );

                    let update_events = relay_path.build_update_client_on_src(update_height)?;

                    if let Some(client_update) = update_events.pop() {
                        batch_messages.push(client_update);
                    }
                }

                AssembledMessages::Src(batch_messages)
            }
            Self::Dst(data) => {
                let mut batch_messages = data.batch_messages();

                if batch_messages.is_empty() {
                    warn!("assemble_msgs() method call on an empty OperationalData!");
                    return Ok(AssembledMessages::Dst(batch_messages));
                }

                // For zero delay we prepend the client update msgs.
                if relay_path.zero_delay() {
                    let update_height = data.proofs_height.map(|h| h.increment());

                    info!(
                        "[{}] prepending {} client update @ height {}",
                        relay_path,
                        self.target(),
                        update_height
                    );

                    let update_events = relay_path.build_update_client_on_dst(update_height)?;

                    if let Some(client_update) = update_events.pop() {
                        batch_messages.push(client_update);
                    }
                }

                AssembledMessages::Dst(batch_messages)
            }
        };

        info!(
            "[{}] assembled batch of {} message(s)",
            relay_path,
            messages.len()
        );

        Ok(messages)
    }
}

impl<Chain, Counterparty> fmt::Display for OperationPayload<Chain, Counterparty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "@{}; {} event(s) & msg(s) in batch",
            self.proofs_height,
            self.batch.len(),
        )
    }
}

impl<SrcChain, DstChain> fmt::Display for SrcOperationPayload<SrcChain, DstChain> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "@{}; {} event(s) & msg(s) in batch",
            self.proofs_height,
            self.batch.len(),
        )
    }
}

impl<SrcChain, DstChain> fmt::Display for DstOperationPayload<SrcChain, DstChain> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "@{}; {} event(s) & msg(s) in batch",
            self.proofs_height,
            self.batch.len(),
        )
    }
}

impl<ChainA, ChainB> fmt::Display for OperationalData<ChainA, ChainB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Src(data) => {
                write!(f, "Op.Data [->Source {}]", data)
            }
            Self::Dst(data) => {
                write!(f, "Op.Data [->Destination {}]", data)
            }
        }
    }
}
