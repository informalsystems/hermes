use std::str::FromStr;
use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::tracking::TrackingId;
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer::link::operational_data::{OperationalData, OperationalDataTarget, TransitMessage};
use ibc_relayer_types::core::ics04_channel::events::{SendPacket, WriteAcknowledgement};
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use once_cell::sync::Lazy;

const NUM_BATCHES: usize = 32;
const TIMEOUT_STRIDE: u64 = 5;
static PORT_ID: Lazy<PortId> = Lazy::new(|| PortId::from_str("transfer").expect("valid port id"));
static CHANNEL_ID: Lazy<ChannelId> =
    Lazy::new(|| ChannelId::from_str("channel-0").expect("valid channel id"));

fn relay_path_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("relay_path_timeout_processing");

    for &batch_size in &[32usize, 64, 128] {
        group.bench_with_input(
            BenchmarkId::new("legacy_clone", batch_size),
            &batch_size,
            |b, &size| {
                b.iter_batched(
                    || build_operational_batches(size),
                    |dataset| {
                        let (_, total) = process_batches_with_clones(dataset);
                        black_box(total);
                    },
                    BatchSize::SmallInput,
                );
            },
        );

        group.bench_with_input(
            BenchmarkId::new("drain_reuse", batch_size),
            &batch_size,
            |b, &size| {
                b.iter_batched(
                    || build_operational_batches(size),
                    |dataset| {
                        let (_, total) = process_batches_with_drain(dataset);
                        black_box(total);
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

fn build_operational_batches(batch_size: usize) -> Vec<OperationalData> {
    (0..NUM_BATCHES)
        .map(|batch_index| {
            let mut odata = OperationalData::new(
                Height::new(0, 10).expect("height"),
                OperationalDataTarget::Destination,
                TrackingId::new_static("bench"),
                Duration::ZERO,
            );

            for entry in 0..batch_size {
                let seq = (batch_index * batch_size + entry + 1) as u64;
                let message = if seq % TIMEOUT_STRIDE == 0 {
                    make_send_packet(seq)
                } else {
                    make_write_ack(seq)
                };

                odata.push(message);
            }

            odata
        })
        .collect()
}

fn make_send_packet(sequence: u64) -> TransitMessage {
    let packet = Packet {
        sequence: Sequence::from(sequence),
        source_port: PORT_ID.clone(),
        source_channel: CHANNEL_ID.clone(),
        destination_port: PORT_ID.clone(),
        destination_channel: CHANNEL_ID.clone(),
        data: vec![0; 32],
        timeout_height: TimeoutHeight::default(),
        timeout_timestamp: Timestamp::none(),
    };

    let event = IbcEvent::SendPacket(SendPacket { packet });

    TransitMessage {
        event_with_height: IbcEventWithHeight::new(
            event,
            Height::new(0, sequence + 1).expect("height"),
        ),
        msg: Any {
            type_url: "bench/send".into(),
            value: sequence.to_le_bytes().to_vec(),
        },
    }
}

fn make_write_ack(sequence: u64) -> TransitMessage {
    let packet = Packet {
        sequence: Sequence::from(sequence),
        source_port: PORT_ID.clone(),
        source_channel: CHANNEL_ID.clone(),
        destination_port: PORT_ID.clone(),
        destination_channel: CHANNEL_ID.clone(),
        data: vec![1; 32],
        timeout_height: TimeoutHeight::default(),
        timeout_timestamp: Timestamp::none(),
    };

    let event = IbcEvent::WriteAcknowledgement(WriteAcknowledgement {
        packet,
        ack: vec![0_u8; 8],
    });

    TransitMessage {
        event_with_height: IbcEventWithHeight::new(
            event,
            Height::new(0, sequence + 1).expect("height"),
        ),
        msg: Any {
            type_url: "bench/ack".into(),
            value: sequence.to_le_bytes().to_vec(),
        },
    }
}

fn build_timeout_msg() -> Any {
    Any {
        type_url: "bench/timeout".into(),
        value: vec![0_u8; 4],
    }
}

fn should_timeout(sequence: &Sequence) -> bool {
    sequence.as_u64() % TIMEOUT_STRIDE == 0
}

fn process_batches_with_clones(mut data: Vec<OperationalData>) -> (Vec<OperationalData>, usize) {
    let mut timed_out: Vec<Vec<TransitMessage>> = vec![Vec::new(); data.len()];
    let mut total_timeouts = 0usize;

    for (idx, odata) in data.iter_mut().enumerate() {
        let mut retain_batch = Vec::new();

        for gm in odata.batch.iter() {
            match &gm.event_with_height.event {
                IbcEvent::SendPacket(event) if should_timeout(&event.packet.sequence) => {
                    total_timeouts += 1;
                    let mut cloned = gm.clone();
                    cloned.msg = build_timeout_msg();
                    timed_out[idx].push(cloned);
                }
                _ => retain_batch.push(gm.clone()),
            }
        }

        odata.batch = retain_batch;
    }

    let scheduled: usize = timed_out.into_iter().map(|v| v.len()).sum();
    (data, total_timeouts + scheduled)
}

fn process_batches_with_drain(mut data: Vec<OperationalData>) -> (Vec<OperationalData>, usize) {
    let mut timed_out: Vec<Vec<TransitMessage>> = vec![Vec::new(); data.len()];
    let mut total_timeouts = 0usize;

    for (idx, odata) in data.iter_mut().enumerate() {
        let mut retain_batch = Vec::with_capacity(odata.batch.len());

        for gm in odata.batch.drain(..) {
            match &gm.event_with_height.event {
                IbcEvent::SendPacket(event) if should_timeout(&event.packet.sequence) => {
                    total_timeouts += 1;
                    let timeout_msg = TransitMessage {
                        event_with_height: gm.event_with_height.clone(),
                        msg: build_timeout_msg(),
                    };
                    timed_out[idx].push(timeout_msg);
                }
                _ => retain_batch.push(gm),
            }
        }

        odata.batch = retain_batch;
    }

    let scheduled: usize = timed_out.into_iter().map(|v| v.len()).sum();
    (data, total_timeouts + scheduled)
}

criterion_group!(benches, relay_path_benchmark);
criterion_main!(benches);
