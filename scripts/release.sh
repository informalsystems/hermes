#!/bin/bash

# release.sh will hopefully allow us to publish all of the necessary crates in
# this repo in the right order. It is assumed that only one person will be
# releasing all crates at the same time.
#
# It has a default set of crates it will publish, which can be overridden by
# way of command line arguments:
#
#   # Release all packages, prompting for each package as to whether to publish
#   ./scripts/release.sh
#
#   # Just release the ibc-proto and ibc crates, but nothing else
#   ./scripts/release.sh ibc-proto ibc

set -e

# A space-separated list of all the crates we want to publish, in the order in
# which they must be published. It's important to respect this order, since
# each subsequent crate depends on one or more of the preceding ones.
DEFAULT_CRATES="ibc-proto ibc ibc-telemetry ibc-relayer ibc-relayer-rest ibc-relayer-cli ibc-test-framework"

# Allows us to override the crates we want to publish.
CRATES=${*:-${DEFAULT_CRATES}}

get_manifest_path() {
  cargo metadata --format-version 1 | jq -r '.packages[]|select(.name == "'"${1}"'")|.manifest_path'
}

get_local_version() {
  cargo metadata --format-version 1 | jq -r '.packages[]|select(.name == "'"${1}"'")|.version'
}

check_version_online() {
  curl -s "https://crates.io/api/v1/crates/${1}" | jq -r '.versions[]|select(.num == "'"${2}"'").updated_at'
}

publish() {
  echo "Publishing crate $1..."
  cargo publish --manifest-path "$(get_manifest_path "${1}")"
  echo ""
}

wait_until_available() {
  echo "Waiting for crate ${1} to become available via crates.io..."
  for retry in {1..5}; do
    sleep 5
    ONLINE_DATE="$(check_version_online "${1}" "${2}")"
    if [ -n "${ONLINE_DATE}" ]; then
      echo "Crate ${crate} is now available online"
      break
    else
      if [ "${retry}" == 5 ]; then
        echo "ERROR: Crate should have become available by now"
        exit 1
      else
        echo "Not available just yet. Waiting a few seconds..."
      fi
    fi
  done
  echo "Waiting an additional 10 seconds for crate to propagate through CDN..."
  sleep 10
}

echo "Attempting to publish crate(s): ${CRATES}"

for crate in ${CRATES}; do
  VERSION="$(get_local_version "${crate}")"
  ONLINE_DATE="$(check_version_online "${crate}" "${VERSION}")"
  echo "${crate} version number: ${VERSION}"
  if [ -n "${ONLINE_DATE}" ]; then
    echo "${crate} ${VERSION} has already been published at ${ONLINE_DATE}, skipping"
    continue
  fi

  publish "${crate}"
  wait_until_available "${crate}" "${VERSION}"
done
