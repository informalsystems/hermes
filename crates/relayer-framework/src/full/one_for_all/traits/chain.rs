use crate::base::one_for_all::traits::batch::OfaBatch;
use crate::base::one_for_all::traits::chain::OfaChain;
use crate::base::one_for_all::traits::telemetry::{OfaTelemetry, OfaTelemetryWrapper};
use crate::full::batch::context::BatchChannel;

pub trait OfaFullChain: OfaChain {
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
