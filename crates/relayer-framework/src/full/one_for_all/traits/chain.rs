use crate::base::one_for_all::traits::chain::OfaBaseChain;
use crate::full::batch::context::BatchChannel;
use crate::full::one_for_all::traits::batch::OfaBatch;
use crate::full::one_for_all::traits::telemetry::{OfaTelemetry, OfaTelemetryWrapper};

pub trait OfaFullChain: OfaBaseChain {
    type BatchContext: OfaBatch<Self>;

    type Telemetry: OfaTelemetry;

    fn batch_channel(
        &self,
    ) -> &BatchChannel<
        <Self::BatchContext as OfaBatch<Self>>::BatchSender,
        <Self::BatchContext as OfaBatch<Self>>::BatchReceiver,
    >;

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry>;
}
