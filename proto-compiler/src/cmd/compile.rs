use std::fs::remove_dir_all;
use std::fs::{copy, create_dir_all};
use std::path::{Path, PathBuf};
use std::process;

use git2::Repository;
use tempdir::TempDir;
use walkdir::WalkDir;

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
    ibc: PathBuf,

    #[argh(option, short = 'o')]
    /// path to output the generated Rust sources into
    out: PathBuf,
}

impl CompileCmd {
    pub fn run(&self) {
        let tmp = TempDir::new("ibc-proto").unwrap();

        Self::output_version(&self.sdk, tmp.as_ref(), "COSMOS_SDK_COMMIT");
        Self::output_version(&self.ibc, tmp.as_ref(), "COSMOS_IBC_COMMIT");
        Self::compile_sdk_protos(&self.sdk, tmp.as_ref());
        Self::compile_ibc_protos(&self.ibc, &self.sdk, tmp.as_ref());
        Self::copy_generated_files(tmp.as_ref(), &self.out);
    }

    fn output_version(dir: &Path, out_dir: &Path, commit_file: &str) {
        let repo = Repository::open(dir).unwrap();
        let commit = repo.head().unwrap();
        let rev = commit.shorthand().unwrap();
        let path = out_dir.join(commit_file);

        std::fs::write(path, rev).unwrap();
    }

    fn compile_ibc_protos(ibc_dir: &Path, sdk_dir: &Path, out_dir: &Path) {
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
            format!("{}/proto/cosmos", sdk_dir.display()),
            format!("{}/third_party/proto", ibc_dir.display()),
        ];

        // List available proto files
        let mut protos: Vec<PathBuf> = vec![];
        for proto_path in &proto_paths {
            println!("Looking for proto files in {:?}", proto_path);
            protos.append(
                &mut WalkDir::new(proto_path)
                    .into_iter()
                    .filter_map(|e| e.ok())
                    .filter(|e| {
                        e.file_type().is_file()
                            && e.path().extension().is_some()
                            && e.path().extension().unwrap() == "proto"
                    })
                    .map(|e| e.into_path())
                    .collect(),
            );
        }

        println!("Found the following protos:");
        // Show which protos will be compiled
        for proto in &protos {
            println!("\t-> {:?}", proto);
        }
        println!("[info ] Compiling..");

        // List available paths for dependencies
        let includes: Vec<PathBuf> = proto_includes_paths.iter().map(PathBuf::from).collect();

        let compilation = tonic_build::configure()
            .build_client(true)
            .build_server(false)
            .format(false)
            .out_dir(out_dir)
            .extern_path(".tendermint", "::tendermint_proto")
            .compile(&protos, &includes);

        match compilation {
            Ok(_) => {
                println!("Successfully compiled proto files");
            }
            Err(e) => {
                println!("Failed to compile:{:?}", e.to_string());
                process::exit(1);
            }
        }
    }

    fn compile_sdk_protos(sdk_dir: &Path, out_dir: &Path) {
        println!(
            "[info ] Compiling Cosmos-SDK .proto files to Rust into '{}'...",
            out_dir.display()
        );

        let root = env!("CARGO_MANIFEST_DIR");

        // Paths
        let proto_paths = [
            format!("{}/../proto/definitions/mock", root),
            format!("{}/proto/cosmos/auth", sdk_dir.display()),
            format!("{}/proto/cosmos/gov", sdk_dir.display()),
            format!("{}/proto/cosmos/tx", sdk_dir.display()),
            format!("{}/proto/cosmos/base", sdk_dir.display()),
            format!("{}/proto/cosmos/staking", sdk_dir.display()),
            format!("{}/proto/cosmos/upgrade", sdk_dir.display()),
        ];

        let proto_includes_paths = [
            format!("{}/../proto", root),
            format!("{}/proto", sdk_dir.display()),
            format!("{}/third_party/proto", sdk_dir.display()),
        ];

        // List available proto files
        let mut protos: Vec<PathBuf> = vec![];
        for proto_path in &proto_paths {
            println!("Looking for proto files in {:?}", proto_path);
            protos.append(
                &mut WalkDir::new(proto_path)
                    .into_iter()
                    .filter_map(|e| e.ok())
                    .filter(|e| {
                        e.file_type().is_file()
                            && e.path().extension().is_some()
                            && e.path().extension().unwrap() == "proto"
                    })
                    .map(|e| e.into_path())
                    .collect(),
            );
        }

        println!("Found the following protos:");
        // Show which protos will be compiled
        for proto in &protos {
            println!("\t-> {:?}", proto);
        }
        println!("[info ] Compiling..");

        // List available paths for dependencies
        let includes: Vec<PathBuf> = proto_includes_paths.iter().map(PathBuf::from).collect();

        let compilation = tonic_build::configure()
            .build_client(true)
            .build_server(false)
            .format(false)
            .out_dir(out_dir)
            .extern_path(".tendermint", "::tendermint_proto")
            .compile(&protos, &includes);

        match compilation {
            Ok(_) => {
                println!("Successfully compiled proto files");
            }
            Err(e) => {
                println!("Failed to compile:{:?}", e.to_string());
                process::exit(1);
            }
        }
    }

    fn copy_generated_files(from_dir: &Path, to_dir: &Path) {
        println!(
            "[info ] Copying generated files into '{}'...",
            to_dir.display()
        );

        // Remove old compiled files
        remove_dir_all(&to_dir).unwrap_or_default();
        create_dir_all(&to_dir).unwrap();

        // Copy new compiled files (prost does not use folder structures)
        let errors = WalkDir::new(from_dir)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file())
            .map(|e| {
                copy(
                    e.path(),
                    format!(
                        "{}/{}",
                        to_dir.display(),
                        &e.file_name().to_os_string().to_str().unwrap()
                    ),
                )
            })
            .filter_map(|e| e.err())
            .collect::<Vec<_>>();

        if !errors.is_empty() {
            for e in errors {
                println!("[error] Error while copying compiled file: {}", e);
            }

            panic!("[error] Aborted.");
        }
    }
}
