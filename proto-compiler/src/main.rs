use std::env::var;
use std::fs::remove_dir_all;
use std::fs::{copy, create_dir_all};
use std::path::{Path, PathBuf};

use git2::Repository;
use tempdir::TempDir;
use walkdir::WalkDir;

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let target_dir = root.join("../proto/src/prost");
    let out_dir = var("OUT_DIR")
        .map(PathBuf::from)
        .or_else(|_| TempDir::new("ibc_proto_out").map(|d| d.into_path()))
        .unwrap();

    let sdk_dir = clone_cosmos_sdk();
    compile_protos(&sdk_dir, &out_dir);
    compile_proto_services(&sdk_dir, &out_dir);
    copy_generated_files(&out_dir, &target_dir);
}

fn clone_cosmos_sdk() -> PathBuf {
    let sdk_dir = var("SDK_DIR").unwrap_or_else(|_| "target/cosmos-sdk".to_string());

    if Path::new(&sdk_dir).exists() {
        println!("[info ] Found Cosmos SDK source at '{}'", sdk_dir);
    } else {
        println!("[info ] Cloning cosmos/cosmos-sdk repository...");

        let url = "https://github.com/cosmos/cosmos-sdk";
        Repository::clone(url, &sdk_dir).unwrap();

        println!("[info ] => Cloned at '{}'", sdk_dir);
    }

    PathBuf::from(sdk_dir)
}

fn compile_protos(sdk_dir: impl AsRef<Path>, out_dir: impl AsRef<Path>) {
    println!(
        "[info ] Compiling .proto files to Rust into '{}'...",
        out_dir.as_ref().display()
    );

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let sdk_dir = sdk_dir.as_ref().to_owned();

    // Paths
    let proto_paths = [
        root.join("../proto/definitions/mock"),
        sdk_dir.join("proto/ibc"),
        sdk_dir.join("proto/cosmos/tx"),
        sdk_dir.join("proto/cosmos/base"),
    ];

    let proto_includes_paths = [
        root.join("../proto"),
        sdk_dir.join("proto"),
        sdk_dir.join("third_party/proto"),
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
    config.out_dir(out_dir.as_ref());
    config.extern_path(".tendermint", "::tendermint_proto");
    config.compile_protos(&protos, &includes).unwrap();

    println!("[info ] => Done!");
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
        sdk_dir.join("proto/cosmos/auth/v1beta1/query.proto")
    ];

    // List available paths for dependencies
    let services = proto_services_path.iter().map(|p| p.as_os_str().to_os_string()).collect::<Vec<_>>();

    // Compile all proto client for GRPC services
    println!("[info ] Compiling proto clients for GRPC services!");
    tonic_build::configure()
        .build_client(true)
        .build_server(false)
        .out_dir(out_dir)
        .compile(&services, &includes).unwrap();

    println!("[info ] => Done!");
}

fn copy_generated_files(from_dir: impl AsRef<Path>, to_dir: impl AsRef<Path>) {
    println!(
        "[info ] Copying generated Rust sources into '{}'...",
        to_dir.as_ref().display()
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
                    to_dir.as_ref().display(),
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

    println!("[info ] => Done!");
}
