use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::relay::traits::context::RelayContext;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::types::aliases::Packet;
use crate::std_prelude::*;

const MAX_RETRY: usize = 3;

pub struct MaxRetryExceeded {
    pub retries: usize,
}

pub trait RetryableError {
    fn is_retryable(&self) -> bool;
}

pub struct RetryRelayer<InRelay> {
    pub phantom: PhantomData<InRelay>,
}

impl<InRelay> RetryRelayer<InRelay> {
    pub fn new(phantom: PhantomData<InRelay>) -> Self {
        Self { phantom }
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
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        for _ in 0..MAX_RETRY {
            let res = InRelay::relay_packet(context, packet).await;

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

        Err(MaxRetryExceeded { retries: MAX_RETRY }.into())
    }
}
