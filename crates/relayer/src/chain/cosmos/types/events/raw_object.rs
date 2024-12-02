use alloc::collections::btree_map::BTreeMap as HashMap;

use ibc_relayer_types::events::Error as EventError;
use ibc_relayer_types::Height;

#[derive(Debug, Clone)]
pub struct RawObject<'a> {
    pub height: Height,
    pub action: String,
    pub idx: usize,
    pub events: &'a HashMap<String, Vec<String>>,
}

impl<'a> RawObject<'a> {
    pub fn new(
        height: Height,
        action: String,
        idx: usize,
        events: &'a HashMap<String, Vec<String>>,
    ) -> RawObject<'a> {
        RawObject {
            height,
            action,
            idx,
            events,
        }
    }
}

pub fn extract_attribute(object: &RawObject<'_>, key: &str) -> Result<String, EventError> {
    let value = object
        .events
        .get(key)
        .ok_or_else(|| EventError::missing_key(key.to_string()))?[object.idx]
        .clone();

    Ok(value)
}

pub fn maybe_extract_attribute(object: &RawObject<'_>, key: &str) -> Option<String> {
    object.events.get(key).map(|tags| tags[object.idx].clone())
}
