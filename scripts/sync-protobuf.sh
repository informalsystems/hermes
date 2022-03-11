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

# We can specify where to clone the git repositories
# for cosmos-sdk and ibc-go. By default they are cloned
# to /tmp/cosmos-sdk.git and /tmp/ibc-go.git.
# We can override this to existing directories
# that already have a clone of the repositories,
# so that there is no need to clone the entire
# repositories over and over again every time
# the script is called.

CACHE_PATH="${XDG_CACHE_HOME:-$HOME/.cache}"
COSMOS_SDK_GIT="${COSMOS_SDK_GIT:-$CACHE_PATH/cosmos/cosmos-sdk.git}"
IBC_GO_GIT="${IBC_GO_GIT:-$CACHE_PATH/ibc-go.git}"


COSMOS_SDK_COMMIT="$(cat proto/src/COSMOS_SDK_COMMIT)"
IBC_GO_COMMIT="$(cat proto/src/IBC_GO_COMMIT)"

echo "COSMOS_SDK_COMMIT: $COSMOS_SDK_COMMIT"
echo "IBC_GO_COMMIT: $IBC_GO_COMMIT"

# Use either --sdk-commit flag for commit ID,
# or --sdk-tag for git tag. Because we can't modify
# proto-compiler to have smart detection on that.

if [[ "$COSMOS_SDK_COMMIT" =~ ^[a-zA-Z0-9]{40}$ ]]
then
	SDK_COMMIT_OPTION="--sdk-commit"
else
	SDK_COMMIT_OPTION="--sdk-tag"
fi

# If the git directories does not exist, clone them as
# bare git repositories so that no local modification
# can be done there.

if [[ ! -e "$COSMOS_SDK_GIT" ]]
then
	echo "Cloning cosmos-sdk source code to as bare git repository to $COSMOS_SDK_GIT"
	git clone --mirror https://github.com/cosmos/cosmos-sdk.git "$COSMOS_SDK_GIT"
else
	echo "Using existing cosmos-sdk bare git repository at $COSMOS_SDK_GIT"
fi

if [[ ! -e "$IBC_GO_GIT" ]]
then
	echo "Cloning ibc-go source code to as bare git repository to $IBC_GO_GIT"
	git clone --mirror https://github.com/cosmos/ibc-go.git "$IBC_GO_GIT"
else
	echo "Using existing ibc-go bare git repository at $IBC_GO_GIT"
fi

# Update the repositories using git fetch. This is so that
# we keep local copies of the repositories up to sync first.
pushd "$COSMOS_SDK_GIT"
git fetch
popd

pushd "$IBC_GO_GIT"
git fetch
popd

# Create a new temporary directory to check out the
# actual source files from the bare git repositories.
# This is so that we do not accidentally use an unclean
# local copy of the source files to generate the protobuf.
COSMOS_SDK_DIR=$(mktemp -d /tmp/cosmos-sdk-XXXXXXXX)

pushd "$COSMOS_SDK_DIR"
git clone "$COSMOS_SDK_GIT" .
git checkout "$COSMOS_SDK_COMMIT"

# We have to name the commit as a branch because
# proto-compiler uses the branch name as the commit
# output. Otherwise it will just output HEAD
git checkout -b "$COSMOS_SDK_COMMIT"
popd

IBC_GO_DIR=$(mktemp -d /tmp/ibc-go-XXXXXXXX)

pushd "$IBC_GO_DIR"
git clone "$IBC_GO_GIT" .
git checkout "$IBC_GO_COMMIT"
git checkout -b "$IBC_GO_COMMIT"
popd

# Remove the existing generated protobuf files
# so that the newly generated code does not
# contain removed files.

rm -rf proto/src/prost
mkdir -p proto/src/prost

cd proto-compiler

cargo build --locked

# Run the proto-compiler twice,
# once for std version with --build-tonic set to true
# and once for no-std version with --build-tonic set to false

cargo run --locked -- compile \
	--sdk "$COSMOS_SDK_DIR" --ibc "$IBC_GO_DIR" --out ../proto/src/prost

# Remove the temporary checkouts of the repositories

rm -rf "$COSMOS_SDK_DIR"
rm -rf "$IBC_GO_DIR"
