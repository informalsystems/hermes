use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::types::aliases::Packet;
use crate::std_prelude::*;

pub struct MaxRetryExceeded {
    pub retries: usize,
}

pub trait RetryableError {
    fn is_retryable(&self) -> bool;
}

pub struct RetryRelayer<InRelay> {
    pub max_retry: usize,
    pub in_relayer: InRelay,
}

impl<InRelay> RetryRelayer<InRelay> {
    pub fn new(max_retry: usize, in_relayer: InRelay) -> Self {
        Self {
            max_retry,
            in_relayer,
        }
    }
}

#[async_trait]
impl<Context, InRelay> PacketRelayer<Context> for RetryRelayer<InRelay>
where
    Context: RelayContext,
    InRelay: PacketRelayer<Context>,
    Context::Error: RetryableError,
    Context::Error: From<MaxRetryExceeded>,
{
    async fn relay_packet(
        &self,
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        for _ in 0..self.max_retry {
            let res = self.in_relayer.relay_packet(context, packet).await;

            match res {
                Ok(()) => {
                    return Ok(());
                }
                Err(e) => {
                    if !e.is_retryable() {
                        return Err(e);
                    }
                }
            }
        }

        Err(MaxRetryExceeded {
            retries: self.max_retry,
        }
        .into())
    }
}
