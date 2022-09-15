//! This crate verifies the correctness of every Hermes command in the guide by:
//! 1. Extracting every line in the guide with '{{#template *templates/commands/hermes*}}', a macro call for mdbook template.
//! 2. Replace every template call with the content of the template. It will replace macro call by what should be an Hermes command.
//! 3. Check that an `EntryPoint` can be created from the command.

use clap::Parser;
use ibc_relayer_cli::entry::EntryPoint;
use lazy_static::lazy_static;
use regex::Regex;
use std::process::exit;
use std::{
    collections::{HashMap, HashSet},
    ffi::OsStr,
    fs::{canonicalize, File},
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};
use walkdir::WalkDir;

#[derive(Debug)]
enum ParseError {
    PathDoesNotExist(std::io::Error),
    IncorrectHermesCommand(clap::Error),
}

impl From<clap::Error> for ParseError {
    fn from(e: clap::Error) -> Self {
        ParseError::IncorrectHermesCommand(e)
    }
}
impl From<std::io::Error> for ParseError {
    fn from(e: std::io::Error) -> Self {
        ParseError::PathDoesNotExist(e)
    }
}

// Constants
lazy_static! {
    // Path to the guide.
    static ref GUIDE_PATH: PathBuf = PathBuf::from("guide/src/");

    // Path to the templates folder where hermes commands templates are defined.
    static ref TEMPLATES_PATH: PathBuf = PathBuf::from("guide/src/templates/commands/hermes/");

    // Map of template path to the content of the template.
    static ref TEMPLATE_MAP: HashMap<PathBuf, String> = build_templates_map();

    // List of directories which should not be visited when checking for correctness.
    static ref EXCLUSIONS: HashSet<&'static str> = HashSet::from(["templates", "assets", "images", "theme"]);

    // Regex to match macro calls in the guide
    static ref TEMPLATE_RE : Regex = Regex::new(r"\s*\{{2}#template (../)*templates/commands/hermes/(?P<template_name>[a-z0-9/\-_\.]+).*").unwrap();

    // Regex to match key=value pairs in the macro calls
    static ref KEY_VALUE : Regex = Regex::new(r"\S+=[^=}]+[ |}]").unwrap();
}

fn build_templates_map() -> HashMap<PathBuf, String> {
    // Builds a map of {template path => content} by reading all the `md` files in the `guide/src/templates/` directory
    let mut templates = HashMap::new();
    for entry in WalkDir::new(TEMPLATES_PATH.as_path()) {
        let entry = entry.expect("Failed to read entry");
        let path = entry.path();
        if path.is_file() && path.extension() == Some(OsStr::new("md")) {
            let content = std::fs::read_to_string(path).unwrap();
            templates.insert(
                canonicalize(path).expect("failed to convert relative path to absolute path"),
                content,
            );
        }
    }
    templates
}

fn build_map_from_macro(line: &str) -> HashMap<String, String> {
    // Builds a map of {argument => value} from a macro call.
    // i.e. `{{#template ../templates/commands/hermes/tx/raw.md arg1="value1" arg2="value2"}}` will return {arg1 => value1, arg2 => value2}
    KEY_VALUE
        .find_iter(line)
        .map(|m| {
            let key_value: Vec<&str> = m.as_str().trim_end_matches('}').split('=').collect();
            (key_value[0].to_string(), key_value[1..].join(""))
        })
        .collect()
}

fn replace_args(line: &str, args: &HashMap<String, String>) -> String {
    // Replace the placeholders in the template's content with the values from the macro call.
    // replace_args(`hermes command [[#argument]]`, {"argument" => "value"})
    // returns `hermes command value`
    let mut line = line.to_string();
    for (key, value) in args {
        line = line.replace(&format!("[[#{key}]]"), value);
    }
    line = line.replace("[[#BINARY hermes]]", "hermes");
    line = line.replace("[[#GLOBALOPTIONS]]", "");
    line = line.replace("[[#OPTIONS]]", "");
    line = line.replace("[[#SUBCOMMAND]]", "");
    line
}

fn get_template_path(line: &str) -> Result<Option<PathBuf>, ParseError> {
    // Checks if the line contains a macro call, if it does then it extracts the template's path as an absolute path.
    // get_template_path("... {{#template my_template}} ...") -> Some(PathBuf("/home/user/ibc-rs/guide/src/templates/commands/hermes/my_template.md"))
    if let Some(captures) = TEMPLATE_RE.captures(line) {
        let template_name = captures
            .name("template_name")
            .expect("Impossible to get template name");
        let mut template_path = TEMPLATES_PATH.clone();
        template_path.push(template_name.as_str());
        // Transform relative path into absolute path.
        return Ok(Some(canonicalize(template_path)?));
    }
    Ok(None)
}

fn check_correctness<'a, T>(command: T) -> Result<(), ParseError>
where
    T: IntoIterator<Item = &'a str>,
    // Returns an error if the command cannot be parsed.
{
    EntryPoint::try_parse_from(command)?;
    Ok(())
}

fn verify_line(line: &str) -> Result<(), ParseError> {
    // If `line` contains a macro call, replace it with the content of the template and check that the command is correct.
    // Returns an error if the command is incorrect.
    if let Some(template_path) = get_template_path(line)? {
        // Extract the absolute path from the macro call
        let template_content = TEMPLATE_MAP.get(template_path.as_path()).unwrap();
        let map = build_map_from_macro(&line);
        let template_replaced = replace_args(template_content, &map);
        check_correctness(template_replaced.split_whitespace())?;
    }
    Ok(())
}

fn verify_file(path: &Path) -> i32 {
    // Verifies that every template macro call in the file can be replaced by a valid Hermes command.
    // Returns the number of invalid commands found.

    let mut error_founds = 0;
    let file = File::open(path);
    let reader =
        BufReader::new(file.unwrap_or_else(|_| panic!("File not found: {}", path.display())));
    let mut line_number = 1;

    for line in reader.lines() {
        let line = line
            .unwrap_or_else(|_| panic!("{} : Failed to read line {}", path.display(), line_number));
        if let Err(e) = verify_line(&line) {
            eprintln!("{}:{}: {:?}", path.display(), line_number, e);
            error_founds += 1;
        }
        line_number += 1;
    }
    error_founds
}

fn main() {
    // Iterate over every markdown file in the guide directory except for the excluded ones
    let number_of_errors = WalkDir::new(GUIDE_PATH.as_path())
        .into_iter() // Iterate over all files in the guide directory
        .filter_entry(|e| {
            !EXCLUSIONS.contains(
                e.file_name()
                    .to_str()
                    .expect("Unwrapping a file_name to str failed."),
            )
        }) // Filter out the excluded directories
        .map(|e| e.expect("Failed to get an entry."))
        .filter(|e| e.file_type().is_file()) // Keep only files
        .filter(|e| e.path().extension() == Some(OsStr::new("md"))) // Keep only markdown files
        .map(|e| verify_file(e.path())) // Verify that all command templates can be parsed to a Hermes command and return the number of errors
        .sum::<i32>(); // Sum the number of errors

    exit(number_of_errors);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_map_from_macro() {
        let line = "    {{#template ../templates/commands/hermes/assistant/create.md name=assistant_name options=--option1 --option2 options3=option3}}";
        let map = build_map_from_macro(line);
        println!("{:#?}", map);
        assert_eq!(map.get("name").unwrap(), "assistant_name ");
        assert_eq!(map.get("options").unwrap(), "--option1 --option2 ");
        assert_eq!(map.get("options3").unwrap(), "option3");
    }

    #[test]
    fn test_replace_args_without_options() {
        let line = "    [[#BINARY hermes]] [[#GLOBALOPTIONS]] assistant [[#OPTIONS]] --flag1 [[#FLAG1]] --flag2 [[#FLAG2]]";
        let expected = "    hermes  assistant  --flag1 flag1_value --flag2 flag2_value";
        let map = HashMap::from(
            [("FLAG1", "flag1_value"), ("FLAG2", "flag2_value")]
                .map(|(k, v)| (k.to_string(), v.to_string())),
        );
        let replaced = replace_args(line, &map);
        assert_eq!(replaced, expected);
    }

    #[test]
    fn test_replace_args_with_options() {
        let line = "    [[#BINARY hermes]] [[#GLOBALOPTIONS]] assistant [[#OPTIONS]] --flag1 [[#FLAG1]] --flag2 [[#FLAG2]]";
        let expected =
            "    hermes  assistant --option1 --option2 --flag1 flag1_value --flag2 flag2_value";
        let map = HashMap::from(
            [
                ("FLAG1", "flag1_value"),
                ("OPTIONS", "--option1 --option2"),
                ("FLAG2", "flag2_value"),
            ]
            .map(|(k, v)| (k.to_string(), v.to_string())),
        );
        let replaced = replace_args(line, &map);
        assert_eq!(replaced, expected);
    }
}
