use std::fs::remove_dir_all;
use std::fs::{copy, create_dir_all};
use std::path::{Path, PathBuf};

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
    #[argh(option, short = 'o')]
    /// path to output the generated Rust sources into
    out: PathBuf,
}

impl CompileCmd {
    pub fn run(&self) {
        let tmp = TempDir::new("ibc-proto").unwrap();

        Self::output_sdk_version(&self.sdk, tmp.as_ref());
        Self::compile_protos(&self.sdk, tmp.as_ref());
        Self::compile_proto_services(&self.sdk, &tmp.as_ref());
        Self::copy_generated_files(tmp.as_ref(), &self.out);
    }

    fn output_sdk_version(sdk_dir: &Path, out_dir: &Path) {
        let repo = Repository::open(sdk_dir).unwrap();
        let commit = repo.head().unwrap();
        let rev = commit.shorthand().unwrap();
        let path = out_dir.join("COSMOS_SDK_COMMIT");

        std::fs::write(path, rev).unwrap();
    }

    fn compile_protos(sdk_dir: &Path, out_dir: &Path) {
        println!(
            "[info ] Compiling .proto files to Rust into '{}'...",
            out_dir.display()
        );

        let root = env!("CARGO_MANIFEST_DIR");

        // Paths
        let proto_paths = [
            format!("{}/../proto/definitions/mock", root),
            format!("{}/proto/ibc", sdk_dir.display()),
            format!("{}/proto/cosmos/tx", sdk_dir.display()),
            format!("{}/proto/cosmos/base", sdk_dir.display()),
            format!("{}/proto/cosmos/staking", sdk_dir.display()),
        ];

        let proto_includes_paths = [
            format!("{}/../proto", root),
            format!("{}/proto", sdk_dir.display()),
            format!("{}/third_party/proto", sdk_dir.display()),
        ];

        // List available proto files
        let mut protos: Vec<PathBuf> = vec![];
        for proto_path in &proto_paths {
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

        // List available paths for dependencies
        let includes: Vec<PathBuf> = proto_includes_paths.iter().map(PathBuf::from).collect();

        // Compile all proto files
        let mut config = prost_build::Config::default();
        config.out_dir(out_dir);
        config.extern_path(".tendermint", "::tendermint_proto");
        config.compile_protos(&protos, &includes).unwrap();
    }

    fn compile_proto_services(sdk_dir: impl AsRef<Path>, out_dir: impl AsRef<Path>) {

        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let sdk_dir = sdk_dir.as_ref().to_owned();

        let proto_includes_paths = [
            root.join("../proto"),
            sdk_dir.join("proto"),
            sdk_dir.join("third_party/proto"),
        ];

        // List available paths for dependencies
        let includes = proto_includes_paths.iter().map(|p| p.as_os_str().to_os_string()).collect::<Vec<_>>();

        let proto_services_path = [
            sdk_dir.join("proto/cosmos/auth/v1beta1/query.proto"),
            sdk_dir.join("proto/cosmos/staking/v1beta1/query.proto"),
            sdk_dir.join("proto/ibc/core/channel/v1/query.proto"),
        ];

        // List available paths for dependencies
        let services = proto_services_path.iter().map(|p| p.as_os_str().to_os_string()).collect::<Vec<_>>();

        // Compile all proto client for GRPC services
        println!("[info ] Compiling proto clients for GRPC services!");
        tonic_build::configure()
            .build_client(true)
            .build_server(false)
            .format(false)
            .out_dir(out_dir)
            .compile(&services, &includes).unwrap();

        println!("[info ] => Done!");
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
