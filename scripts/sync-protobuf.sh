#!/usr/bin/env bash

set -eou pipefail

# syn-protobuf.sh is a bash script to sync the protobuf
# files using the proto-compiler project. It will check
# out the protobuf files from the git versions specified in
# proto/src/prost/COSMOS_SDK_COMMIT and
# proto/src/prost/IBC_GO_COMMIT. If you want to sync
# the protobuf files to a newer version, modify the
# relevant files with the new commit IDs.

# This script should be run from the root directory of ibc-rs

COSMOS_SDK_COMMIT="$(cat proto/src/COSMOS_SDK_COMMIT)"
IBC_GO_COMMIT="$(cat proto/src/IBC_GO_COMMIT)"

echo "COSMOS_SDK_COMMIT: $COSMOS_SDK_COMMIT"
echo "IBC_GO_COMMIT: $IBC_GO_COMMIT"

# Remove the existing generated protobuf files
# so that the newly generated code does not
# contain removed files.

rm -rf proto/src/prost
mkdir -p proto/src/prost

cd proto

buf generate --verbose --template buf.gen.yaml \
	--path proto/cosmos \
    "https://github.com/cosmos/cosmos-sdk.git#ref=${COSMOS_SDK_COMMIT}"

buf generate --verbose --template buf.gen.yaml \
	--path proto/ibc \
    "https://github.com/cosmos/ibc-go.git#ref=${IBC_GO_COMMIT}"
