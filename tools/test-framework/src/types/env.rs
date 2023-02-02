/*!
   Types for exporting test setup information into environment variables.
*/

use core::convert::AsRef;
use itertools::Itertools;
use std::collections::BTreeMap;
use std::fs::write;
use std::path::Path;

use crate::error::Error;
use crate::types::tagged::*;

/**
    This trait is implemented by data types that can export the contained
    information as environment variables.

    Using this, test framework can export them as `.env` files, which users
    can then manually `source` them in the terminal to interact with the
    test chains and relayer when the tests are suspended.
*/
pub trait ExportEnv {
    /**
       Export the environment variables using the given [`EnvWriter`].
    */
    fn export_env(&self, writer: &mut impl EnvWriter);
}

/**
   The exported environment variables are stored in a data type that
   implements this trait.
*/
pub trait EnvWriter {
    /**
       Write an environment variable with the given key and value.

       Note that overlapping keys will be overridden with the new value.
    */
    fn write_env(&mut self, key: &str, value: &str);
}

/**
   Create an [`EnvWriter`] that adds a prefix to the keys of the exported envs.
*/
pub fn prefix_writer<'a, Writer: EnvWriter>(
    prefix: &str,
    writer: &'a mut Writer,
) -> impl EnvWriter + 'a {
    PrefixEnvWriter {
        prefix: prefix.to_string(),
        writer,
    }
}

/**
   A wrapper that implements [`EnvWriter`] by adding a prefix to the key
   before writing to the underlying [`EnvWriter`].
*/
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

/**
   Retrieve the environment variables exported by a type implementing
   `ExportEnv`, and export them as a string containing the variables
   in the form of `KEY=VALUE` on each line.
*/
pub fn format_env(exporter: &impl ExportEnv) -> String {
    let mut envs = BTreeMap::new();
    exporter.export_env(&mut envs);

    envs.iter()
        .map(|(key, value)| format!("{key}={value}"))
        .join("\n")
}

/**
   Retrieve the environment variables exported by a type implementing
   `ExportEnv`, and save them as a `.env` file to the given file path.
*/
pub fn write_env(path: impl AsRef<Path>, exporter: &impl ExportEnv) -> Result<(), Error> {
    write(path, format_env(exporter))?;

    Ok(())
}
