//! This crate verifies the correctness of every Hermes command in the guide by:
//! 1. Extracting every line in the guide with '{{#template *templates/commands/hermes*}}', a macro call for mdbook template.
//! 2. Replace every template call with the content of the template. It will replace the macro call with what should be a Hermes command.
//! 3. Check that an `EntryPoint` can be created from the command.

use clap::Parser;
use ibc_relayer_cli::entry::EntryPoint;
use lazy_static::lazy_static;
use mdbook_template::replace_template;
use mdbook_template::utils::SystemFileReader;
use regex::Regex;
use std::{
    collections::HashSet,
    ffi::OsStr,
    fs::File,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};
use walkdir::WalkDir;

#[derive(Debug)]
enum ParseError {
    IncorrectHermesCommand(clap::Error),
}

impl From<clap::Error> for ParseError {
    fn from(e: clap::Error) -> Self {
        ParseError::IncorrectHermesCommand(e)
    }
}

// Constants
lazy_static! {
    // Path to the guide.
    static ref GUIDE_PATH: PathBuf = PathBuf::from("guide/src/");

    // Path to the templates folder where hermes commands templates are defined.
    static ref TEMPLATES_PATH: PathBuf = PathBuf::from("guide/src/templates/commands/hermes/");

    // List of directories which should not be visited when checking for correctness.
    static ref EXCLUSIONS: HashSet<&'static str> = HashSet::from(["templates", "assets", "images", "theme"]);

    // Regex to match macro calls in the guide
    static ref TEMPLATE_RE: Regex = Regex::new(r"\{{2}#template.*templates/commands/hermes/.*\}\}").unwrap();

    // FileReader for mdbook_template
    static ref FILEREADER: SystemFileReader = SystemFileReader::default();
}

fn check_correctness<'a, T>(command: T) -> Result<(), ParseError>
where
    T: IntoIterator<Item = &'a str>,
    // Returns an error if the command cannot be parsed.
{
    EntryPoint::try_parse_from(command)?;
    Ok(())
}

/// Extracts macro calls from a command, replace them with the content of the template and check that the command is correct.
/// Returns the number of errors encountered.
fn verify_line(line: &str, path: &Path, line_number: i32) -> i32 {
    let parent = path.parent().unwrap_or_else(|| Path::new(&*GUIDE_PATH));
    let mut errors_found = 0;

    TEMPLATE_RE.find_iter(line).for_each(|m| {
        let template = m.as_str();
        let template_replaced = replace_template(template, &*FILEREADER, parent, "", 0);
        if let Err(e) = check_correctness(template_replaced.split_whitespace()) {
            eprintln!("{}:{}: {:?}", path.display(), line_number, e);
            errors_found += 1;
        }
    });
    errors_found
}

/// Verifies that every template macro call in the file can be replaced by a valid Hermes command.
/// Returns the number of invalid commands found.
fn verify_file(path: &Path) -> i32 {
    let mut errors_found = 0;
    let file = File::open(path);
    let reader =
        BufReader::new(file.unwrap_or_else(|_| panic!("File not found: {}", path.display())));
    let mut line_number = 1;

    for line in reader.lines() {
        let line = line
            .unwrap_or_else(|_| panic!("{} : Failed to read line {}", path.display(), line_number));
        errors_found += verify_line(&line, path, line_number);
        line_number += 1;
    }
    errors_found
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
        .filter(|e| e.file_type().is_file() && e.path().extension() == Some(OsStr::new("md"))) // Keep only markdown files
        .map(|e| verify_file(e.path())) // Verify that all command templates can be parsed to a Hermes command and return the number of errors
        .sum::<i32>(); // Sum the number of errors
    if number_of_errors > 0 {
        panic!("{} errors found.", number_of_errors);
    }
}
