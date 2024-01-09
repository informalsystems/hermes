use std::ops::RangeInclusive;

use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum Error {
    #[error("Invalid sequence number: {0}")]
    InvalidSequenceNumber(String),

    #[error("Invalid range: {0}")]
    InvalidRange(String),
}

/// Parse a list of ranges over sequence numbers, separated by commas.
///
/// - Each item in the list is either a single sequence number, or a range of sequence numbers.
/// - A range is specified as `start..end`, where `start` and `end` are sequence numbers.
/// - If `start` is omitted, the range starts at the minimum sequence number.
/// - If `end` is omitted, the range ends at the maximum sequence number.
/// - If both `start` and `end` are omitted, the range sastifies any sequence number.
///
/// # Examples
/// - `1`                           Single sequence number `1`
/// - `1,2,3`                       Sequence numbers `1`, `2`, and `3`
/// - `..20`                        Sequence numbers less than or equal to `20`
/// - `10..`                        Sequence numbers greater than or equal to `10`
/// - `10..20`                      Sequence numbers `10`, `11`, `12`, ..., `20`
/// - `2,4..6,12,14..17,21,30..`    Sequence numbers `2`, `4`, `5`, `6`, `12`, `14`, `15`, `16`, `17`, `21`, `30`, `31`, `32`, ...
/// - `30..,21,12,14..17,4..6,2`    Same as previous
/// - `..`                          Any sequence number
pub fn parse_seq_ranges(s: &str) -> Result<Vec<RangeInclusive<Sequence>>, Error> {
    s.split(',').map(parse_seq_range).collect()
}

/// Parse a range of sequence numbers.
///
/// - This can be a single sequence number, or a range of sequence numbers.
/// - A range is specified as `start..end`, where `start` and `end` are sequence numbers.
/// - If `start` is omitted, the range starts at the minimum sequence number.
/// - If `end` is omitted, the range ends at the maximum sequence number.`
/// - If both `start` and `end` are omitted, the range sastifies any sequence number.
///
/// # Examples
/// - `1`                           Single sequence number `1`
/// - `1..2`                        Single sequence number `1`
/// - `..20`                        Sequence numbers strictly less than `20`
/// - `10..`                        Sequence numbers greater than or equal to `10`
/// - `10..20`                      Sequence numbers `10`, `11`, `12`, ..., `19`
/// - `..`                          Any sequence number
pub fn parse_seq_range(s: &str) -> Result<RangeInclusive<Sequence>, Error> {
    if s.contains("..") {
        parse_range(s)
    } else {
        parse_single(s)
    }
}

fn parse_int(s: &str) -> Result<Sequence, Error> {
    s.parse::<Sequence>()
        .map_err(|_| Error::InvalidSequenceNumber(s.to_string()))
}

fn parse_single(s: &str) -> Result<RangeInclusive<Sequence>, Error> {
    parse_int(s).map(|num| num..=num)
}

fn parse_range(s: &str) -> Result<RangeInclusive<Sequence>, Error> {
    match s.split_once("..") {
        // ..
        Some(("", "")) => Ok(Sequence::MIN..=Sequence::MAX),

        // ..end
        Some(("", end)) => {
            let end = parse_int(end)?;
            Ok(Sequence::MIN..=end)
        }

        // start..
        Some((start, "")) => {
            let start = parse_int(start)?;
            Ok(start..=Sequence::MAX)
        }

        // start..end
        Some((start, end)) => {
            let start = parse_int(start)?;
            let end = parse_int(end)?;
            Ok(start..=end)
        }

        // not a range
        None => Err(Error::InvalidRange(s.to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(range: RangeInclusive<u64>) -> RangeInclusive<Sequence> {
        Sequence::from(*range.start())..=Sequence::from(*range.end())
    }

    #[test]
    fn parse_seq_ranges_works() {
        let tests = [
            ("1", vec![r(1..=1)]),
            ("1,2", vec![r(1..=1), r(2..=2)]),
            ("1,2,3", vec![r(1..=1), r(2..=2), r(3..=3)]),
            ("1..3", vec![r(1..=3)]),
            ("..3", vec![r(u64::MIN..=3)]),
            ("3..", vec![r(3..=u64::MAX)]),
            ("..", vec![r(u64::MIN..=u64::MAX)]),
            ("1..3,4", vec![r(1..=3), r(4..=4)]),
            ("1,2..4", vec![r(1..=1), r(2..=4)]),
            ("1..3,4..6", vec![r(1..=3), r(4..=6)]),
            (
                "..3,4..,..",
                vec![r(u64::MIN..=3), r(4..=u64::MAX), r(u64::MIN..=u64::MAX)],
            ),
            (
                "1..,..6,7..7",
                vec![r(1..=u64::MAX), r(u64::MIN..=6), r(7..=7)],
            ),
        ];

        for (input, expected) in tests {
            let actual = parse_seq_ranges(input).unwrap();
            assert_eq!(actual, expected);
        }

        let fails = ["1-1", "1.1", "-1", "1..2..3", "1..-2", "-1.22"];

        for fail in fails {
            assert!(parse_seq_ranges(fail).is_err());
        }
    }
}
