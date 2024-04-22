{ nixpkgs }:
let
  rust-bin =
    nixpkgs.rust-bin.stable.latest.default.override
      {
        targets = [ "wasm32-unknown-unknown" ];
      };
in
nixpkgs.rustPlatform.buildRustPackage {
  name = "ibc-client-tendermint-cw";

  src = nixpkgs.fetchFromGitHub {
    owner = "cosmos";
    repo = "ibc-rs";
    rev = "d0f7cc41c413bdb1e801acaa566f3e7cf06c2c93";
    hash = "sha256-LBuP+t7M5KL4a5tbGlALq1B0G3UV3Nqvh4r1X/BgGK0=";
  };

  cargoLock = {
    lockFile = ./ibc-rs.Cargo.lock;
  };

  postPatch = ''
    ln -s ${./ibc-rs.Cargo.lock} Cargo.lock
  '';

  nativeBuildInputs = [
    rust-bin
  ];

  doCheck = false;

  buildPhase = ''
    RUSTFLAGS='-C link-arg=-s' cargo build -p ibc-client-tendermint-cw --target wasm32-unknown-unknown --release --lib --locked
  '';

  installPhase = ''
    mkdir -p $out
    cp target/wasm32-unknown-unknown/release/ibc_client_tendermint_cw.wasm $out/
  '';
}
