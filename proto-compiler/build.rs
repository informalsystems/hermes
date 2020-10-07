use git2::Repository;
use std::env::var;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

fn main() {
    let sdk_dir = var("SDK_DIR").unwrap_or_else(|_| "target/cosmos-sdk".to_string());
    if !Path::new(&sdk_dir).exists() {
        let url = "https://github.com/cosmos/cosmos-sdk";
        Repository::clone(url, &sdk_dir).unwrap();
    }

    // Paths
    let proto_paths = [
        //"../proto/definitions/mock".to_string(),
        format!("{}/proto/ibc", sdk_dir),
        format!("{}/proto/cosmos/tx", sdk_dir),
        format!("{}/proto/cosmos/base", sdk_dir),
    ];
    let proto_includes_paths = [
        //"../proto/definitions".to_string(),
        format!("{}/proto", sdk_dir),
        format!("{}/third_party/proto", sdk_dir),
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
    let mut pb = prost_build::Config::new();
    pb.extern_path(".tendermint", "::tendermint_proto");
    pb.compile_protos(&protos, &includes).unwrap();
}
