//! A group of messages ready for getting submitted to a chain
//! as a single transaction.
//!
//! A [`Partition`] is a unit for grouping together
//! multiple messages in a way that preserves
//! the preconfigured `max_msg_num` and the
//! `max_tx_size` chain parameters.
#[derive(Clone, Debug)]
pub struct Partition {
    // The maximum allowed length of this partition in terms of number of messages.
    max_len: usize,

    // The maximum allowed size of this partition, in bytes.
    max_bytes: usize,

    // The current size of this partition, in number of items.
    len: usize,

    // The current size of the partition, in bytes.
    bytes: usize,

    // The underlying messages comprised in this partition.
    items: Vec<prost_types::Any>,
}

impl Partition {
    /// Creates a new [`Partition`] with the given parameters,
    /// containing a single message.
    fn create(message: prost_types::Any, max_len: usize, max_bytes: usize) -> Self {
        Partition {
            max_len,
            max_bytes,
            len: 1,
            bytes: get_bytes_size(&message),
            items: vec![message],
        }
    }

    /// Pushes a message into the current [`Partition`],
    /// modifying it in place. Returns `None` if successful.
    /// If it cannot accommodate the message,
    /// the [`Partition`] remains unmodified, and this method
    /// returns instead `Some` new [`Partition`] with the given
    /// message.
    fn push_or_create(&mut self, message: prost_types::Any) -> Option<Self> {
        let message_size = get_bytes_size(&message);
        if self.len + 1 > self.max_len || self.bytes + message_size > self.max_bytes {
            Some(Self::create(message, self.max_len, self.max_bytes))
        } else {
            self.len += 1;
            self.bytes += message_size;
            self.items.push(message);
            None
        }
    }

    /// Drains all of the messages contained in this [`Partition`].
    pub fn messages(self) -> Vec<prost_types::Any> {
        self.items
    }
}

fn get_bytes_size(message: &prost_types::Any) -> usize {
    let mut buf = Vec::new();
    prost::Message::encode(message, &mut buf).unwrap();
    buf.len()
}

/// Given a vector of messages, groups the messages together
/// into one or multiple [`Partition`]s, and returns an iterator
/// over the resulting partitions.
pub fn partition_msgs(
    all: Vec<prost_types::Any>,
    max_msgs: usize,
    max_bytes: usize,
) -> impl Iterator<Item = Partition> {
    let res = all.into_iter().fold(vec![], |mut accumulator, next_msg| {
        match accumulator.last_mut() {
            None => {
                // Initialization step is a special case.
                // No partition exists yet: create one & push it.
                accumulator.push(Partition::create(next_msg, max_msgs, max_bytes));
            }
            Some(partition) => {
                if let Some(new_partition) = partition.push_or_create(next_msg) {
                    // If `push_or_create` returned `Some` new partition, the last one was full.
                    // Append the new partition.
                    accumulator.push(new_partition)
                }
            }
        }
        accumulator
    });

    res.into_iter()
}
