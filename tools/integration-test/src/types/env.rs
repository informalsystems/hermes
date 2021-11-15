use core::convert::AsRef;
use itertools::Itertools;
use std::collections::BTreeMap;
use std::fs::write;
use std::path::Path;

use crate::error::Error;
use crate::types::tagged::*;

pub fn prefix_writer<'a, Writer: EnvWriter>(
    prefix: &str,
    writer: &'a mut Writer,
) -> impl EnvWriter + 'a {
    PrefixEnvWriter {
        prefix: prefix.to_string(),
        writer,
    }
}

pub trait EnvWriter {
    fn write_env(&mut self, key: &str, value: &str);
}

pub struct PrefixEnvWriter<'a, Writer> {
    prefix: String,
    writer: &'a mut Writer,
}

impl EnvWriter for BTreeMap<String, String> {
    fn write_env(&mut self, key: &str, value: &str) {
        self.insert(key.to_string(), value.to_string());
    }
}

impl<'a, Writer: EnvWriter> EnvWriter for PrefixEnvWriter<'a, Writer> {
    fn write_env(&mut self, key: &str, value: &str) {
        self.writer
            .write_env(&format!("{}_{}", self.prefix, key), value);
    }
}

pub trait ExportEnv {
    fn export_env(&self, writer: &mut impl EnvWriter);
}

impl<Tag, Value: ExportEnv> ExportEnv for MonoTagged<Tag, Value> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.value().export_env(writer);
    }
}

impl<TagA, TagB, Value: ExportEnv> ExportEnv for DualTagged<TagA, TagB, Value> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.value().export_env(writer);
    }
}

impl<'a, T1: ExportEnv, T2: ExportEnv> ExportEnv for (&'a T1, &'a T2) {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.0.export_env(writer);
        self.1.export_env(writer);
    }
}

pub fn format_env(exporter: &impl ExportEnv) -> String {
    let mut envs = BTreeMap::new();
    exporter.export_env(&mut envs);

    envs.iter()
        .map(|(key, value)| format!("{}={}", key, value))
        .join("\n")
}

pub fn write_env(path: impl AsRef<Path>, exporter: &impl ExportEnv) -> Result<(), Error> {
    write(path, format_env(exporter))?;

    Ok(())
}
