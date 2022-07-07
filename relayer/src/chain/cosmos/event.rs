use tendermint::abci::responses::Event;

pub fn split_events_by_messages(in_events: Vec<Event>) -> Vec<Vec<Event>> {
    let mut out_events = Vec::new();
    let mut current_events = Vec::new();
    let mut first_message_event_found = false;

    for event in in_events.into_iter() {
        if event.type_str == "message"
            && event.attributes.len() == 1
            && event.attributes[0].key.as_ref() == "action"
        {
            if first_message_event_found {
                out_events.push(current_events);
            } else {
                first_message_event_found = true;
            }

            current_events = vec![event];
        } else if first_message_event_found {
            current_events.push(event);
        }
    }

    if !current_events.is_empty() {
        out_events.push(current_events);
    }

    out_events
}
