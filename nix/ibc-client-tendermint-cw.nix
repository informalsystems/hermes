{ nixpkgs }:
let
  rustWithWasmTarget =
    nixpkgs.rust-bin.stable.latest.default.override
      {
        targets = [ "wasm32-unknown-unknown" ];
      };

  rustWasmPlatform = nixpkgs.makeRustPlatform {
    cargo = rustWithWasmTarget;
    rustc = rustWithWasmTarget;
  };
in
rustWasmPlatform.buildRustPackage {
  name = "ibc-client-tendermint-cw";

  src = nixpkgs.fetchFromGitHub {
    owner = "cosmos";
    repo = "ibc-rs";
    rev = "68268ec16c218421964de022699e51e4f40f8c84";
    hash = "sha256-cgHBluU6T2nNOhd3CmKBiENJ6O/TE9rc+RbUmaCj1rQ=";
  };

  cargoLock = {
    lockFile = ./ibc-rs.Cargo.lock;
  };

  postPatch = ''
    ln -s ${./ibc-rs.Cargo.lock} Cargo.lock
  '';

  doCheck = false;

  buildPhase = ''
    RUSTFLAGS='-C link-arg=-s' cargo build -p ibc-client-tendermint-cw --target wasm32-unknown-unknown --release --lib --locked
  '';

  installPhase = ''
    mkdir -p $out
    cp target/wasm32-unknown-unknown/release/ibc_client_tendermint_cw.wasm $out/
  '';
}
