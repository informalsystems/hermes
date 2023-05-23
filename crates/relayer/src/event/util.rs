use tendermint::abci::Event;

pub fn dedupe(events: Vec<Event>) -> Vec<Event> {
    use itertools::Itertools;
    use std::hash::{Hash, Hasher};

    #[derive(Clone)]
    struct HashEvent(Event);

    impl PartialEq for HashEvent {
        fn eq(&self, other: &Self) -> bool {
            // NOTE: We don't compare on the index because it is not deterministic
            // NOTE: We need to check the length of the attributes in order
            // to not miss any attribute
            self.0.kind == other.0.kind
                && self.0.attributes.len() == other.0.attributes.len()
                && self
                    .0
                    .attributes
                    .iter()
                    .zip(other.0.attributes.iter())
                    .all(|(a, b)| a.key == b.key && a.value == b.value)
        }
    }

    impl Eq for HashEvent {}

    impl Hash for HashEvent {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.kind.hash(state);

            for attr in &self.0.attributes {
                // NOTE: We don't hash the index because it is not deterministic
                attr.key.hash(state);
                attr.value.hash(state);
            }
        }
    }

    events
        .into_iter()
        .map(HashEvent)
        .unique()
        .map(|e| e.0)
        .collect()
}
