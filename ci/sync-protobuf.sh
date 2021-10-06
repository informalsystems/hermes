#!/usr/bin/env bash

set -eoux pipefail

COSMOS_SDK_COMMIT=$(cat proto/src/prost/COSMOS_SDK_COMMIT)
COSMOS_IBC_COMMIT=$(cat proto/src/prost/COSMOS_IBC_COMMIT)

echo "COSMOS_SDK_COMMIT: $COSMOS_SDK_COMMIT"
echo "COSMOS_IBC_COMMIT: $COSMOS_IBC_COMMIT"

if [[ "$COSMOS_SDK_COMMIT" =~ ^[a-zA-Z0-9]{40}$ ]]
then
	SDK_COMMIT_OPTION="--sdk-commit"
else
	SDK_COMMIT_OPTION="--sdk-tag"
fi

rm -rf /tmp/cosmos

cd proto-compiler

cargo build --locked

cargo run --locked -- clone --out /tmp/cosmos \
	"$SDK_COMMIT_OPTION" "$COSMOS_SDK_COMMIT" \
	--ibc-go-commit "$COSMOS_IBC_COMMIT"

cargo run --locked -- compile-std \
	--sdk /tmp/cosmos/sdk --ibc /tmp/cosmos/ibc --out ../proto/src/prost
