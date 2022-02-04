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
    ibc: Option<PathBuf>,

    #[argh(option, short = 'o')]
    /// path to output the generated Rust sources into
    out: PathBuf,

    #[argh(option)]
    /// generate tonic client code
    build_tonic: bool,
}

impl CompileCmd {
    pub fn run(&self) {
        let tmp_sdk = TempDir::new("ibc-proto-sdk").unwrap();
        Self::compile_sdk_protos(
            &self.sdk,
            tmp_sdk.as_ref(),
            self.ibc.clone(),
            self.build_tonic,
        );

        match &self.ibc {
            None => {
                println!("[info ] Omitting the IBC-go repo");
                Self::copy_generated_files(tmp_sdk.as_ref(), None, &self.out);
            }
            Some(ibc_path) => {
                let tmp_ibc = TempDir::new("ibc-proto-ibc-go").unwrap();
                Self::compile_ibc_protos(ibc_path, tmp_ibc.as_ref(), self.build_tonic);

                // Merge the generated files into a single directory, taking care not to overwrite anything
                Self::copy_generated_files(tmp_sdk.as_ref(), Some(tmp_ibc.as_ref()), &self.out);
            }
        }
    }

    fn compile_ibc_protos(ibc_dir: &Path, out_dir: &Path, build_tonic: bool) {
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
        let attrs_serde_eq = "#[derive(::serde::Serialize, ::serde::Deserialize, Eq)]";

        let compilation = tonic_build::configure()
            .build_client(build_tonic)
            .build_server(false)
            .format(true)
            .out_dir(out_dir)
            .extern_path(".tendermint", "::tendermint_proto")
            .type_attribute(".ics23.LeafOp", attrs_serde_eq)
            .type_attribute(".ics23.InnerOp", attrs_serde_eq)
            .type_attribute(".ics23.ProofSpec", attrs_serde_eq)
            .type_attribute(".ics23.InnerSpec", attrs_serde_eq)
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

    fn compile_sdk_protos(
        sdk_dir: &Path,
        out_dir: &Path,
        ibc_dep: Option<PathBuf>,
        build_tonic: bool,
    ) {
        println!(
            "[info ] Compiling Cosmos-SDK .proto files to Rust into '{}'...",
            out_dir.display()
        );

        let root = env!("CARGO_MANIFEST_DIR");

        // Paths
        let proto_paths = vec![
            format!("{}/../proto/definitions/mock", root),
            format!("{}/proto/cosmos/auth", sdk_dir.display()),
            format!("{}/proto/cosmos/gov", sdk_dir.display()),
            format!("{}/proto/cosmos/tx", sdk_dir.display()),
            format!("{}/proto/cosmos/base", sdk_dir.display()),
            format!("{}/proto/cosmos/staking", sdk_dir.display()),
            format!("{}/proto/cosmos/upgrade", sdk_dir.display()),
        ];

        let mut proto_includes_paths = vec![
            format!("{}/../proto", root),
            format!("{}/proto", sdk_dir.display()),
            format!("{}/third_party/proto", sdk_dir.display()),
        ];

        if let Some(ibc_dir) = ibc_dep {
            // Use the IBC proto files from the SDK
            proto_includes_paths.push(format!("{}/proto", ibc_dir.display()));
        }

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
            .build_client(build_tonic)
            .build_server(false)
            .format(true)
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

    fn copy_generated_files(from_dir_sdk: &Path, from_dir_ibc_opt: Option<&Path>, to_dir: &Path) {
        println!(
            "[info ] Copying generated files into '{}'...",
            to_dir.display()
        );

        // Remove old compiled files
        remove_dir_all(&to_dir).unwrap_or_default();
        create_dir_all(&to_dir).unwrap();

        // Copy new compiled files (prost does not use folder structures)
        // Copy the SDK files first
        let errors_sdk = WalkDir::new(from_dir_sdk)
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

        if !errors_sdk.is_empty() {
            for e in errors_sdk {
                println!("[error] Error while copying SDK-compiled file: {}", e);
            }

            panic!("[error] Aborted.");
        }

        if let Some(from_dir_ibc) = from_dir_ibc_opt {
            // Copy the IBC-go files second, double-checking if anything is overwritten
            let errors_ibc = WalkDir::new(from_dir_ibc)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file())
            .map(|e| {
                let generated_fname = e.file_name().to_owned().into_string().unwrap();
                let prefix = &generated_fname[0..6];

                let target_fname = format!(
                    "{}/{}",
                    to_dir.display(),
                    generated_fname,
                );

                // If it's a cosmos-relevant file and it exists, we should not overwrite it.
                if Path::new(&target_fname).exists() && prefix.eq("cosmos") {
                    let original_cosmos_file = std::fs::read(target_fname.clone()).unwrap();
                    let new_cosmos_file = std::fs::read(e.path()).unwrap();
                    if original_cosmos_file != new_cosmos_file {
                        println!(
                            "[warn ] Cosmos-related file exists already {}! Ignoring the one generated from IBC-go {:?}",
                            target_fname, e.path()
                        );
                    }
                    Ok(0)
                } else {
                    copy(
                        e.path(),
                        target_fname,
                    )
                }
            })
            .filter_map(|e| e.err())
            .collect::<Vec<_>>();

            if !errors_ibc.is_empty() {
                for e in errors_ibc {
                    println!("[error] Error while copying IBC-go compiled file: {}", e);
                }

                panic!("[error] Aborted.");
            }
        }
    }
}
