use std::fs::remove_dir_all;
use std::fs::{copy, create_dir_all};
use std::path::{Path, PathBuf};
use std::ffi::OsStr;

use git2::Repository;
use tempdir::TempDir;
use walkdir::{WalkDir, DirEntry};
use eyre::{eyre, Report as Error};

use argh::FromArgs;
#[derive(Debug, FromArgs)]
#[argh(subcommand, name = "compile")]
/// Compile
pub struct CompileCmd {
    #[argh(option, short = 's')]
    /// path to the Cosmos SDK
    sdk: PathBuf,

    #[argh(option, short = 'i')]
    /// path to the Cosmos IBC proto files
    ibc: Option<PathBuf>,

    #[argh(option, short = 'o')]
    /// path to output the generated Rust sources into
    out: PathBuf,
}

impl CompileCmd {
    pub fn run(&self) -> Result<(), Error> {
        run_cmd(&self.sdk, &self.ibc, &self.out)
    }
}

fn run_cmd(sdk_src: &Path, ibc_src: &Option<PathBuf>, out: &Path) -> Result<(), Error>
{
    let tmp_sdk = TempDir::new("ibc-proto-sdk")?;
    compile_sdk_protos(sdk_src, tmp_sdk.as_ref(), ibc_src.clone())?;

    match ibc_src {
        None => {
            println!("[info ] Omitting the IBC-go repo");
            copy_generated_files(tmp_sdk.as_ref(), None, &out)?;
        }
        Some(ibc_path) => {
            let tmp_ibc = TempDir::new("ibc-proto-ibc-go")?;

            compile_ibc_protos(&ibc_path, tmp_ibc.as_ref())?;

            // Merge the generated files into a single directory, taking care not to overwrite anything
            copy_generated_files(tmp_sdk.as_ref(), Some(tmp_ibc.as_ref().to_owned()), &out)?;

            output_version(&ibc_path, out, "COSMOS_IBC_COMMIT")?;
        }
    }

    output_version(sdk_src, out, "COSMOS_SDK_COMMIT")?;

    Ok(())
}

fn build_tonic_with_client(
    out_dir: &Path,
    protos: &Vec<PathBuf>,
    includes: &Vec<PathBuf>,
    with_client: bool,
) -> Result<(), std::io::Error>
{
    create_dir_all(out_dir)?;

    tonic_build::configure()
        .build_client(with_client)
        .build_server(false)
        .format(true)
        .out_dir(out_dir)
        .extern_path(".tendermint", "::tendermint_proto")
        .compile(protos, includes)
}

fn build_tonic(
    out_dir: &Path,
    protos: &Vec<PathBuf>,
    includes: &Vec<PathBuf>,
) -> Result<(), std::io::Error>
{
    build_tonic_with_client(
        &out_dir.join("std"),
        protos, includes, true)?;

    build_tonic_with_client(
        &out_dir.join("no_std"),
        protos, includes, false)?;

    Ok(())
}

fn list_files_in_dir(dir: impl AsRef<Path>)
    -> Result<Vec<DirEntry>, Error>
{
    let files_and_dirs = WalkDir::new(dir)
        .into_iter()
        .collect::<Result<Vec<DirEntry>, _>>()?;

    let files = files_and_dirs.into_iter()
        .filter(|f| f.file_type().is_file())
        .collect();

    Ok(files)
}

fn list_protobuf_files(
    proto_paths: &[String],
) -> Result<Vec<PathBuf>, Error>
{
    let mut protos: Vec<PathBuf> = vec![];
    for proto_path in proto_paths {
        println!("Looking for proto files in {:?}", proto_path);

        let mut proto_files = list_files_in_dir(proto_path)?
            .into_iter()
            .filter(|f| {
                f.path().extension() == Some(OsStr::new("proto"))
            })
            .map(|f| f.into_path())
            .collect::<Vec<_>>();

        protos.append(&mut proto_files);
    }

    Ok(protos)
}

fn output_version(dir: &Path, out_dir: &Path, commit_file: &str)
    -> Result<(), Error>
{
    let repo = Repository::open(dir)?;
    let commit = repo.head()?;
    let rev = commit.shorthand()
        .ok_or_else(|| eyre!("expect commit.shorthand to present"))?;

    let path = out_dir.join(commit_file);

    std::fs::write(path, rev)?;

    Ok(())
}

fn compile_ibc_protos(ibc_dir: &Path, out_dir: &Path)
    -> Result<(), Error>
{
    println!(
        "[info ] Compiling IBC .proto files to Rust into '{}'...",
        out_dir.display()
    );

    // Paths
    let proto_paths = [
        // ibc-go proto files
        format!("{}/proto/ibc", ibc_dir.display()),
    ];

    let proto_includes_paths = [
        format!("{}/proto", ibc_dir.display()),
        format!("{}/third_party/proto", ibc_dir.display()),
    ];

    let protos = list_protobuf_files(&proto_paths)?;

    println!("Found the following protos:");
    // Show which protos will be compiled
    for proto in &protos {
        println!("\t-> {:?}", proto);
    }
    println!("[info ] Compiling..");

    // List available paths for dependencies
    let includes: Vec<PathBuf> = proto_includes_paths.iter().map(PathBuf::from).collect();

    build_tonic(&out_dir, &protos, &includes)?;

    println!("Successfully compiled proto files");

    Ok(())
}

fn compile_sdk_protos(sdk_dir: &Path, out_dir: &Path, ibc_dep: Option<PathBuf>)
    -> Result<(), Error>
{
    println!(
        "[info ] Compiling Cosmos-SDK .proto files to Rust into '{}'...",
        out_dir.display()
    );

    let root = env!("CARGO_MANIFEST_DIR");

    let sdk_dir_path = sdk_dir.display();

    // Paths
    let proto_paths = vec![
        format!("{}/../proto/definitions/mock", root),
        format!("{}/proto/cosmos/auth", sdk_dir_path),
        format!("{}/proto/cosmos/gov", sdk_dir_path),
        format!("{}/proto/cosmos/tx", sdk_dir_path),
        format!("{}/proto/cosmos/base", sdk_dir_path),
        format!("{}/proto/cosmos/staking", sdk_dir_path),
        format!("{}/proto/cosmos/upgrade", sdk_dir_path),
    ];


    let mut proto_includes_paths = vec![
        format!("{}/../proto", root),
        format!("{}/proto", sdk_dir_path),
        format!("{}/third_party/proto", sdk_dir_path),
    ];

    if let Some(ibc_dir) = ibc_dep {
        // Use the IBC proto files from the SDK
        proto_includes_paths.push(format!("{}/proto", ibc_dir.display()),);
    }

    let protos = list_protobuf_files(&proto_paths)?;

    println!("Found the following protos:");

    // Show which protos will be compiled
    for proto in &protos {
        println!("\t-> {:?}", proto);
    }

    println!("[info ] Compiling..");

    // List available paths for dependencies
    let includes: Vec<PathBuf> = proto_includes_paths.iter().map(PathBuf::from).collect();

    build_tonic(out_dir, &protos, &includes)?;

    println!("Successfully compiled proto files");

    Ok(())
}

fn copy_generated_files(from_dir_sdk: &Path, from_dir_ibc_opt: Option<PathBuf>, to_dir: &Path)
    -> Result<(), Error>
{
    do_copy_generated_files(
        &from_dir_sdk.join("std"),
        from_dir_ibc_opt.clone().map(|p| p.join("std")),
        &to_dir.join("std")
    )?;

    do_copy_generated_files(
        &from_dir_sdk.join("no_std"),
        from_dir_ibc_opt.map(|p| p.join("no_std")),
        &to_dir.join("no_std")
    )?;


    Ok(())
}

fn do_copy_generated_files(from_dir_sdk: &Path, from_dir_ibc_opt: Option<PathBuf>, to_dir: &Path)
    -> Result<(), Error>
{
    println!(
        "[info ] Copying generated files into '{}'...",
        to_dir.display()
    );

    // Remove old compiled files
    if to_dir.exists() {
        remove_dir_all(&to_dir)?;
    }

    create_dir_all(&to_dir)?;

    let files = list_files_in_dir(from_dir_sdk)?;

    // Copy new compiled files (prost does not use folder structures)
    // Copy the SDK files first
    for file in files {
        copy(
            file.path(),
            to_dir.join(file.file_name()),
        )?;
    }

    if let Some(from_dir_ibc) = from_dir_ibc_opt {
        let files = list_files_in_dir(from_dir_ibc)?;

        for file in files {
            let file_name: &Path = file.file_name().as_ref();
            let target_path = to_dir.join(file.file_name());

            // If it's a cosmos-relevant file and it exists, we should not overwrite it.
            if Path::new(&target_path).exists() && file_name.starts_with("cosmos") {
                let original_cosmos_file = std::fs::read(&target_path)?;
                let new_cosmos_file = std::fs::read(file.path())?;

                if original_cosmos_file != new_cosmos_file {
                    println!(
                        "[warn ] Cosmos-related file exists already {}! Ignoring the one generated from IBC-go {:?}",
                        target_path.display(), file.path()
                    );
                }
            } else {
                copy(
                    file.path(),
                    target_path,
                )?;
            }
        }
    }

    Ok(())
}
