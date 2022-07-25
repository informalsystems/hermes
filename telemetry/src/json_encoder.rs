use std::io::{self, Write};

use prometheus::Result;
use prometheus::proto::{self, MetricFamily, MetricType};

use prometheus::{Encoder};
use serde_json::{Map, Value, json};

/// The text format of metric family.
pub const TEXT_FORMAT: &str = "text/plain; version=0.0.4";

const POSITIVE_INF: &str = "+Inf";
const QUANTILE: &str = "quantile";

/// An implementation of an [`Encoder`] that converts a [`MetricFamily`] proto message
/// into json format.

#[derive(Debug, Default)]
pub struct JsonEncoder;

impl JsonEncoder {
    /// Create a new text encoder.
    pub fn new() -> JsonEncoder {
        JsonEncoder
    }
    /// Appends metrics to a given `String` buffer.
    ///
    /// This is a convenience wrapper around `<JsonEncoder as Encoder>::encode`.
    pub fn encode_utf8(&self, metric_families: &[MetricFamily], buf: &mut String) -> Result<()> {
        // Note: it's important to *not* re-validate UTF8-validity for the
        // entirety of `buf`. Otherwise, repeatedly appending metrics to the
        // same `buf` will lead to quadratic behavior. That's why we use
        // `WriteUtf8` abstraction to skip the validation.
        self.encode_impl(metric_families, &mut StringBuf(buf))?;
        Ok(())
    }
    /// Converts metrics to `String`.
    ///
    /// This is a convenience wrapper around `<JsonEncoder as Encoder>::encode`.
    pub fn encode_to_string(&self, metric_families: &[MetricFamily]) -> Result<String> {
        let mut buf = String::new();
        self.encode_utf8(metric_families, &mut buf)?;
        Ok(buf)
    }

    fn encode_impl(
        &self,
        metric_families: &[MetricFamily],
        writer: &mut dyn WriteUtf8,
    ) -> Result<()> {

        let mut map = Map::new();

        for mf in metric_families {
            
            // Add entry for the metric
            let name : &str = mf.get_name();
            
            let mut mf_map = Map::new();

            // Add Help
            let help : &str = mf.get_help();
            mf_map.insert("help".to_string(), json!{help}); 

            // Write `# TYPE` header.
            let metric_type : MetricType = mf.get_field_type();
            let lowercase_type = json!(format!("{:?}", metric_type).to_lowercase());
            mf_map.insert("type".to_string(), lowercase_type); 

            let mut debug_counter = 0;

            for m in mf.get_metric() {
                println!("{}", debug_counter);
                debug_counter += 1;         // TODO : Remove
                // Metric
                match metric_type {
                    MetricType::COUNTER => {
                        mf_map.insert("counter".to_string(), json!(m.get_counter().get_value()));
                        extra_info(&mut mf_map, m);
                        // f64
                    }
                    MetricType::GAUGE => {
                        mf_map.insert("gauge".to_string(), json!(m.get_gauge().get_value()));
                        extra_info(&mut mf_map, m);
                        // f64
                    }
                    MetricType::HISTOGRAM => {
                        let h = m.get_histogram();
                        let mut upper_bounds : Vec<Value> = vec![];
                        let mut cumulative_counts : Vec<Value> = vec![];
                        let mut inf_seen = false;
                        
                        for b in h.get_bucket() {
                            let upper_bound = b.get_upper_bound();           // f64
                            let cumulative_count = b.get_cumulative_count(); // f64

                            upper_bounds.push(json!(upper_bound));
                            cumulative_counts.push(json!(cumulative_count));

                            if upper_bound.is_sign_positive() && upper_bound.is_infinite() {
                                inf_seen = true;
                            }
                        }
                        if !inf_seen {
                            upper_bounds.push(json!(POSITIVE_INF));
                            cumulative_counts.push(json!(h.get_sample_count()));
                        }
                        let names = [
                            "cumulative_counts".to_string(),
                            "upper_bounds".to_string(),
                            "sum".to_string(),
                            "counts".to_string()
                        ];

                        let values = [
                            json!(cumulative_counts),
                            json!(upper_bounds),
                            json!(h.get_sample_sum()),
                            json!(h.get_sample_count())
                        ];
                        names.into_iter().zip(values.into_iter()).map(|(key, value)| mf_map.insert(key, value));
                        extra_info(&mut mf_map, m);
                    }

                    MetricType::SUMMARY => {
                        let s = m.get_summary();
                        let mut quantiles = vec![];
                        let mut values = vec![];

                        for q in s.get_quantile() {
                            quantiles.push(json!(q.get_quantile()));
                            values.push(q.get_value());
                        }

                        let names = [
                            "sum".to_string(),
                            "quantiles".to_string()
                        ];

                        let values = [
                            json!(s.get_sample_sum()),
                            json!(s.get_sample_count())
                        ];
                        names.into_iter().zip(values.into_iter()).map(|(key, value)| mf_map.insert(key, value));
                        extra_info(&mut mf_map, m);
                    }
                    MetricType::UNTYPED => {
                        unimplemented!();
                    }
                }
            }
            map.insert(name.to_string(), json!(mf_map));
        }

        let x = serde_json::to_string(&map).unwrap();
        println!{"{}", &x};
        writer.write_all(x.as_str())?;
        Ok(())
    }
    
}

impl Encoder for JsonEncoder {
    fn encode<W: Write>(&self, metric_families: &[MetricFamily], writer: &mut W) -> Result<()> {
        self.encode_impl(metric_families, &mut *writer)
    }

    fn format_type(&self) -> &str {
        TEXT_FORMAT
    }
}


// names and values must be of the same length
fn extra_info(
    map : &mut Map<String, Value>,
    mc: &proto::Metric
) -> () {

    let timestamp = mc.get_timestamp_ms();
    if timestamp != 0 {
        map.insert("timestamp".to_string(), json!(timestamp));
    }

    for lp in mc.get_label() {
        map.insert(lp.get_name().to_string(), json!(lp.get_value()));
    }
}





trait WriteUtf8 {
    fn write_all(&mut self, text: &str) -> io::Result<()>;
}

impl<W: Write> WriteUtf8 for W {
    fn write_all(&mut self, text: &str) -> io::Result<()> {
        Write::write_all(self, text.as_bytes())
    }
}

/// Coherence forbids to impl `WriteUtf8` directly on `String`, need this
/// wrapper as a work-around.
struct StringBuf<'a>(&'a mut String);

impl WriteUtf8 for StringBuf<'_> {
    fn write_all(&mut self, text: &str) -> io::Result<()> {
        self.0.push_str(text);
        Ok(())
    }
}
