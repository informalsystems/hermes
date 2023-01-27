// Copyright 2019 TiKV Project Authors. Licensed under Apache-2.0.

use std::collections::BTreeMap;
use std::io::{self, Write};

use prometheus::proto::{self, MetricFamily, MetricType};
use prometheus::{Encoder, Error, Result};

use serde::Serialize;

/// The JSON format of metric family.
pub const JSON_FORMAT: &str = "application/json";

const POSITIVE_INF: &str = "+Inf";
const QUANTILE: &str = "quantile";

/// An implementation of an [`Encoder`] that converts a [`MetricFamily`] proto message
/// into JSON format.
#[derive(Debug, Default)]
pub struct JsonEncoder;

#[derive(Default, Serialize)]
struct JsonFamilies {
    families: Vec<JsonFamily>,
}

#[derive(Serialize)]
struct JsonFamily {
    name: String,
    desc: String,
    r#type: String,
    metrics: Vec<JsonMetric>,
}

#[derive(Serialize)]
#[serde(tag = "type", rename_all = "lowercase")]
enum JsonMetric {
    Counter(Sample),
    Gauge(Sample),
    Histogram {
        buckets: Vec<Sample>,
        sum: Sample,
        count: Sample,
    },
    Summary {
        samples: Vec<Sample>,
        count: Sample,
        sum: Sample,
    },
}

#[derive(Serialize)]
struct Sample {
    name: String,
    value: f64,
    timestamp: Option<i64>,
    labels: BTreeMap<String, String>,
}

impl JsonEncoder {
    /// Create a new text encoder.
    pub fn new() -> Self {
        Self
    }

    fn encode_json(&self, metric_families: &[MetricFamily]) -> Result<JsonFamilies> {
        let mut families = JsonFamilies::default();

        for mf in metric_families {
            let name = mf.get_name();
            let metric_type = mf.get_field_type();

            let mut family = JsonFamily {
                name: name.to_string(),
                desc: mf.get_help().to_string(),
                r#type: format!("{metric_type:?}").to_lowercase(),
                metrics: Vec::default(),
            };

            for m in mf.get_metric() {
                match metric_type {
                    MetricType::COUNTER => {
                        let sample = get_sample(name, None, m, None, m.get_counter().get_value())?;
                        family.metrics.push(JsonMetric::Counter(sample));
                    }
                    MetricType::GAUGE => {
                        let sample = get_sample(name, None, m, None, m.get_gauge().get_value())?;
                        family.metrics.push(JsonMetric::Gauge(sample));
                    }
                    MetricType::HISTOGRAM => {
                        let h = m.get_histogram();

                        let mut buckets = Vec::new();
                        let mut inf_seen = false;

                        for b in h.get_bucket() {
                            let upper_bound = b.get_upper_bound();

                            let bucket = get_sample(
                                name,
                                Some("_bucket"),
                                m,
                                Some(("le", &upper_bound.to_string())),
                                b.get_cumulative_count() as f64,
                            )?;

                            buckets.push(bucket);

                            if upper_bound.is_sign_positive() && upper_bound.is_infinite() {
                                inf_seen = true;
                            }
                        }

                        if !inf_seen {
                            let bucket = get_sample(
                                name,
                                Some("_bucket"),
                                m,
                                Some(("le", POSITIVE_INF)),
                                h.get_sample_count() as f64,
                            )?;

                            buckets.push(bucket);
                        }

                        let sum = get_sample(name, Some("_sum"), m, None, h.get_sample_sum())?;
                        let count =
                            get_sample(name, Some("_count"), m, None, h.get_sample_count() as f64)?;

                        family.metrics.push(JsonMetric::Histogram {
                            buckets,
                            sum,
                            count,
                        });
                    }
                    MetricType::SUMMARY => {
                        let s = m.get_summary();

                        let mut samples = Vec::new();
                        for q in s.get_quantile() {
                            let sample = get_sample(
                                name,
                                None,
                                m,
                                Some((QUANTILE, &q.get_quantile().to_string())),
                                q.get_value(),
                            )?;

                            samples.push(sample);
                        }

                        let sum = get_sample(name, Some("_sum"), m, None, s.get_sample_sum())?;
                        let count =
                            get_sample(name, Some("_count"), m, None, s.get_sample_count() as f64)?;

                        family.metrics.push(JsonMetric::Summary {
                            samples,
                            count,
                            sum,
                        });
                    }
                    MetricType::UNTYPED => {
                        unimplemented!();
                    }
                }
            }

            families.families.push(family);
        }

        Ok(families)
    }
}

impl Encoder for JsonEncoder {
    fn encode<W: Write>(&self, metric_families: &[MetricFamily], writer: &mut W) -> Result<()> {
        let json = self.encode_json(metric_families)?;

        serde_json::to_writer(writer, &json)
            .map_err(|e| Error::Io(io::Error::new(io::ErrorKind::Other, e)))
    }

    fn format_type(&self) -> &str {
        JSON_FORMAT
    }
}

/// `write_sample` writes a single sample in text format to `writer`, given the
/// metric name, an optional metric name postfix, the metric proto message
/// itself, optionally an additional label name and value (use empty strings if
/// not required), and the value. The function returns the number of bytes
/// written and any error encountered.
fn get_sample(
    name: &str,
    name_postfix: Option<&str>,
    mc: &proto::Metric,
    additional_label: Option<(&str, &str)>,
    value: f64,
) -> Result<Sample> {
    let mut name = name.to_string();
    if let Some(postfix) = name_postfix {
        name.push_str(postfix);
    }

    let labels = label_pairs_to_text(mc.get_label(), additional_label)?;
    let timestamp = Some(mc.get_timestamp_ms()).filter(|&ts| ts != 0);

    Ok(Sample {
        name,
        labels,
        value,
        timestamp,
    })
}

fn label_pairs_to_text(
    pairs: &[proto::LabelPair],
    additional_label: Option<(&str, &str)>,
) -> Result<BTreeMap<String, String>> {
    if pairs.is_empty() && additional_label.is_none() {
        return Ok(BTreeMap::default());
    }

    let mut labels = BTreeMap::new();
    for lp in pairs {
        labels.insert(lp.get_name().to_string(), lp.get_value().to_string());
    }

    if let Some((name, value)) = additional_label {
        labels.insert(name.to_string(), value.to_string());
    }

    Ok(labels)
}
