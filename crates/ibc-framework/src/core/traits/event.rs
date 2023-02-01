use crate::core::traits::sync::Async;

pub trait HasEventTypes: Async {
    type Event: Async;
}

pub trait HasEventEmitter: HasEventTypes {
    fn emit_event(&self, event: &Self::Event);
}
