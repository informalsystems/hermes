/*
  This file defines the database schema for the PostgresQL ("psql") event sink
  implementation in Tendermint. The operator must create a database and install
  this schema before using the database to index events.
 */

-- The blocks table records metadata about each block.
-- The block record does not include its events or transactions (see tx_results).
CREATE TABLE blocks (
  rowid      BIGSERIAL PRIMARY KEY,

  height     BIGINT NOT NULL,
  chain_id   VARCHAR NOT NULL,

  -- When this block header was logged into the sink, in UTC.
  created_at TIMESTAMPTZ NOT NULL,

  UNIQUE (height, chain_id)
);

-- Index blocks by height and chain, since we need to resolve block IDs when
-- indexing transaction records and transaction events.
CREATE INDEX idx_blocks_height_chain ON blocks(height, chain_id);

-- The tx_results table records metadata about transaction results.  Note that
-- the events from a transaction are stored separately.
CREATE TABLE tx_results (
  rowid BIGSERIAL PRIMARY KEY,

  -- The block to which this transaction belongs.
  block_id BIGINT NOT NULL REFERENCES blocks(rowid),
  -- The sequential index of the transaction within the block.
  index INTEGER NOT NULL,
  -- When this result record was logged into the sink, in UTC.
  created_at TIMESTAMPTZ NOT NULL,
  -- The hex-encoded hash of the transaction.
  tx_hash VARCHAR NOT NULL,
  -- The protobuf wire encoding of the TxResult message.
  tx_result BYTEA NOT NULL,

  UNIQUE (block_id, index)
);

-- Index the foreign key
CREATE INDEX idx_tx_results_block_id ON tx_results(block_id);

-- Index tx results by hash
CREATE INDEX idx_tx_results_hash ON tx_results(tx_hash);

-- The events table records events. All events (both block and transaction) are
-- associated with a block ID; transaction events also have a transaction ID.
CREATE TABLE events (
  rowid BIGSERIAL PRIMARY KEY,

  -- The block and transaction this event belongs to.
  -- If tx_id is NULL, this is a block event.
  block_id BIGINT NOT NULL REFERENCES blocks(rowid),
  tx_id    BIGINT NULL REFERENCES tx_results(rowid),

  -- The application-defined type label for the event.
  type VARCHAR NOT NULL
);

-- Index the foreign keys
CREATE INDEX idx_events_block_id ON events(block_id);
CREATE INDEX idx_events_tx_id ON events(tx_id);

-- Index columns used in queries
CREATE INDEX idx_events_type ON events(type);

-- The attributes table records event attributes.
CREATE TABLE attributes (
   event_id      BIGINT NOT NULL REFERENCES events(rowid),
   key           VARCHAR NOT NULL, -- bare key
   composite_key VARCHAR NOT NULL, -- composed type.key
   value         VARCHAR NULL,

   UNIQUE (event_id, key)
);

-- Index the foreign key
CREATE INDEX idx_attributes_event_id ON attributes(event_id);

-- Index columns used together in queries
CREATE INDEX idx_attributes_key_value ON attributes(key, value);
CREATE INDEX idx_attributes_composite_key_value ON attributes(composite_key, value);

-- A joined view of events and their attributes. Events that do not have any
-- attributes are represented as a single row with empty key and value fields.
CREATE VIEW event_attributes AS
  SELECT block_id, tx_id, type, key, composite_key, value
  FROM events LEFT JOIN attributes ON (events.rowid = attributes.event_id);

-- A joined view of all block events (those having tx_id NULL).
CREATE VIEW block_events AS
  SELECT blocks.rowid as block_id, height, chain_id, type, key, composite_key, value
  FROM blocks JOIN event_attributes ON (blocks.rowid = event_attributes.block_id)
  WHERE event_attributes.tx_id IS NULL;

-- A joined view of all transaction events.
CREATE VIEW tx_events AS
  SELECT height, index, chain_id, type, key, composite_key, value, tx_results.created_at
  FROM blocks JOIN tx_results ON (blocks.rowid = tx_results.block_id)
  JOIN event_attributes ON (tx_results.rowid = event_attributes.tx_id)
  WHERE event_attributes.tx_id IS NOT NULL;

-- A joined view of all IBC packet transaction events.
CREATE VIEW ibc_packet_src_events AS SELECT * FROM (
    SELECT tx_id, type, value AS packet_src_port FROM event_attributes WHERE key = 'packet_src_port'
    ) src_port
    NATURAL JOIN (
        SELECT tx_id, value AS packet_src_channel FROM event_attributes WHERE key = 'packet_src_channel'
        ) src_channel
    NATURAL JOIN (
        SELECT tx_id, value AS packet_sequence FROM event_attributes WHERE key = 'packet_sequence'
        ) seq
ORDER BY seq.packet_sequence, src_port.tx_id, src_port.type, src_port.packet_src_port, src_channel.packet_src_channel;

CREATE VIEW ibc_tx_packet_events AS SELECT * FROM ibc_packet_src_events JOIN (
    SELECT rowid, tx_hash, tx_result FROM tx_results) tx_result ON (ibc_packet_src_events.tx_id = tx_result.rowid);

-- A joined view of all IBC packet block events. These are the events included in Begin/End Block.
-- `ibc_block_events` does NOT include the Tx events and `ibc_tx_packet_events` does NOT include block events.
CREATE VIEW ibc_block_events AS SELECT * FROM (
    SELECT block_id, type, value AS packet_src_port FROM block_events WHERE key = 'packet_src_port'
    ) src_port
    NATURAL JOIN (
        SELECT block_id, value AS packet_src_channel FROM block_events WHERE key = 'packet_src_channel'
        ) src_channel
    NATURAL JOIN (
        SELECT block_id, value AS packet_sequence FROM event_attributes WHERE key = 'packet_sequence'
        ) seq
    NATURAL JOIN (
        SELECT block_id, value AS packet_dst_port FROM block_events WHERE key = 'packet_dst_port'
        ) dst_port
    NATURAL JOIN (
        SELECT block_id, value AS packet_dst_channel FROM block_events WHERE key = 'packet_dst_channel'
        ) dst_channel
    NATURAL JOIN (
        SELECT block_id, value AS packet_timeout_height FROM block_events WHERE key = 'packet_timeout_height'
    ) packet_timeout_height
        NATURAL JOIN (
        SELECT block_id, value AS packet_timeout_timestamp FROM block_events WHERE key = 'packet_timeout_timestamp'
    ) packet_timeout_timestamp
    NATURAL JOIN (
        SELECT block_id, value AS packet_data FROM block_events WHERE key = 'packet_data'
    ) packet_data
    NATURAL JOIN (
        SELECT block_id, value AS packet_ack FROM block_events WHERE key = 'packet_ack'
    ) packet_ack
ORDER BY seq.packet_sequence, src_port.block_id;

-- A joined view of all IBC client transaction events.
CREATE VIEW ibc_client_events AS SELECT * FROM (
 SELECT tx_id, type, value AS client_id FROM event_attributes WHERE key = 'client_id'
) rel_client_id
NATURAL JOIN (
 SELECT tx_id, value AS consensus_height FROM event_attributes WHERE key = 'consensus_height'
) rel_consensus_height
ORDER BY rel_client_id.tx_id, rel_client_id.type, rel_consensus_height.consensus_height;

CREATE VIEW ibc_tx_client_events AS SELECT * FROM ibc_client_events
  JOIN (
    SELECT rowid, tx_hash, tx_result FROM tx_results
  ) tx_result
  ON (ibc_client_events.tx_id = tx_result.rowid);

