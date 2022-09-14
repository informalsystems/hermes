use clap::Parser;
use ibc_relayer_cli::entry::EntryPoint;
use lazy_static::lazy_static;
use regex::Regex;
use std::{
    collections::{HashMap, HashSet},
    ffi::OsStr,
    fs::{canonicalize, File},
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};
use walkdir::WalkDir;
use std::process::exit;


lazy_static! {
    static ref GUIDE_PATH: PathBuf = PathBuf::from("../../guide/src/");
    static ref TEMPLATES_PATH: PathBuf = PathBuf::from("../../guide/src/templates/commands/hermes/");

    // List of directories which should not be visited
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
    // Builds a map of {argument => value}
    KEY_VALUE
        .find_iter(line)
        .map(|m| {
            let key_value: Vec<&str> = m.as_str().trim_end_matches("}").split('=').collect();
            (
                key_value[0].to_string(),
                key_value[1..].join("").to_string(),
            )
        })
        .collect()
}

fn replace_args(line: &str, args: &HashMap<String, String>) -> String {
    // Expects the content of a template file and replaces the arguments with the values provided in the HashMap (i.e):
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

fn verify_file(path: &Path, template_map: &HashMap<PathBuf, String>) -> i32 {
    // Verifies that every template macro call in the file can be replaced by a valid Hermes command.
    // Returns the number of invalid commands found.

    let mut output = 0;
    // Check that all templates are used in the guide can be replaced by a correct command
    let file = File::open(path);
    let reader =
        BufReader::new(file.expect(format!("File not found: {}", path.display()).as_str()));
    let mut line_number = 1;

    for line in reader.lines() {
        let line = line.expect("Failed to read line");
        if let Some(captures) = TEMPLATE_RE.captures(line.as_str()) {
            // Retrieve the template reference
            let template_name = captures
                .name("template_name")
                .expect("Impossible to get template name");
            let mut template_path = TEMPLATES_PATH.clone();
            template_path.push(template_name.as_str());

            if let Ok(template_path) = canonicalize(&template_path) {
                let template_content = template_map.get(template_path.as_path()).unwrap();
                let map = build_map_from_macro(&line);
                let template_replaced = replace_args(template_content, &map);

                if let Err(_) = EntryPoint::try_parse_from(template_replaced.split_whitespace()) {
                    eprintln!(
                        "{} : Line {} - Failed to parse command {}",
                        path.display(),
                        line_number,
                        template_replaced.as_str()
                    );
                    output = 1;
                }
            } else {
                eprintln!(
                    "{} : Line {} - path does not exist: {}",
                    path.display(),
                    line_number,
                    template_path.display()
                );
                output = 1;
            }
        }
        line_number += 1;
    }
    output
}

fn main() {
    let templates = build_templates_map();

    // Iterate over every markdown file in the guide directory except for the excluded ones
    let number_of_errors = WalkDir::new(GUIDE_PATH.as_path())
        .into_iter()
        .filter_entry(|e| {
            !EXCLUSIONS.contains(
                e.file_name()
                    .to_str()
                    .expect("Unwrapping a file_name to str failed."),
            )
        })
        .map(|e| e.expect("Failed to get an entry."))
        .filter(|e| e.file_type().is_file())
        .filter(|e| e.path().extension() == Some(OsStr::new("md")))
        .map(|e| verify_file(e.path(), &templates))
        .sum::<i32>();
    
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
        let map = HashMap::from([("FLAG1", "flag1_value"), ("FLAG2", "flag2_value")].map(|(k, v)| (k.to_string(), v.to_string())));
        let replaced = replace_args(line, &map);
        assert_eq!(replaced, expected);
    }

    #[test]
    fn test_replace_args_with_options(){
        let line = "    [[#BINARY hermes]] [[#GLOBALOPTIONS]] assistant [[#OPTIONS]] --flag1 [[#FLAG1]] --flag2 [[#FLAG2]]";
        let expected = "    hermes  assistant --option1 --option2 --flag1 flag1_value --flag2 flag2_value";
        let map = HashMap::from([("FLAG1", "flag1_value"), ("OPTIONS", "--option1 --option2"), ("FLAG2", "flag2_value")].map(|(k, v)| (k.to_string(), v.to_string())));
        let replaced = replace_args(line, &map);
        assert_eq!(replaced, expected);
    }
}