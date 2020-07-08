extern crate prost_build;

fn main() {
    prost_build::compile_protos(&["src/proto/ibc/connection/query.proto"], &["src/proto"]).unwrap();
}