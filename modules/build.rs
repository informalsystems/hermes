extern crate prost_build;

fn main() {
    prost_build::compile_protos(&["src/proto/connection.proto"], &["src/proto"]).unwrap();
}
