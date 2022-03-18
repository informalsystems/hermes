use prost_types::Any;

use crate::error::Error;

pub fn batch_messages(
    messages: Vec<Any>,
    max_message_count: usize,
    max_tx_size: usize,
) -> Result<Vec<Vec<Any>>, Error> {
    let mut batches = vec![];

    let mut current_count = 0;
    let mut current_size = 0;
    let mut current_batch = vec![];

    for message in messages.into_iter() {
        current_count += 1;
        current_size += message_size(&message)?;
        current_batch.push(message);

        if current_count >= max_message_count || current_size >= max_tx_size {
            let insert_batch = current_batch.drain(..).collect();
            batches.push(insert_batch);
            current_count = 0;
            current_size = 0;
        }
    }

    if !current_batch.is_empty() {
        batches.push(current_batch);
    }

    Ok(batches)
}

pub fn message_size(message: &Any) -> Result<usize, Error> {
    let mut buf = Vec::new();

    prost::Message::encode(message, &mut buf)
        .map_err(|e| Error::protobuf_encode("Message".into(), e))?;

    Ok(buf.len())
}
