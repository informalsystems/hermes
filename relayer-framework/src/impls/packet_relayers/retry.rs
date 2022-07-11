use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::packet_relayer::PacketRelayer;
use crate::traits::relay_context::RelayContext;
use crate::types::aliases::Packet;

pub struct MaxRetryExceeded {
    pub retries: usize,
}

pub trait RetryableError {
    fn is_retryable(&self) -> bool;
}

pub struct RetryRelayer<InRelay> {
    pub in_relayer: InRelay,
    pub max_retry: usize,
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
