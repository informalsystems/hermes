#!/bin/sh

##############################
## Script setup
##############################

# Fail if there are any errors
set -eu

# Run in a subfolder, not in your $HOME (safeguard against accidental .hermes-deletions)
test "$HOME" != "$(pwd)"
# But if hermes was not run locally, we're going to overcome the issue of not having a --home parameter
test -e $HOME/.hermes || ln -s $(pwd)/.hermes $HOME/.hermes

EXPECTED_HERMES_VERSION=0.2.0
DOCKER_IMAGE="informaldev/hermes:${EXPECTED_HERMES_VERSION}"
HERMES="docker run --rm -v $(pwd)/.hermes:/home/hermes/.hermes --net=host --entrypoint /usr/bin/hermes ${DOCKER_IMAGE}"

##############################
## Create paths on the networks
##############################

while read -r line;
do
  VALID="$(echo "$line" | grep '^[ ]*[0-9]\+[ ]\+[0-9]\+[ ]*$' || echo "")"
  test -n "$VALID" || continue
  i="$(echo "$line" | grep -o '[0-9]\+' | head -1)"
  j="$(echo "$line" | grep -o '[0-9]\+' | tail -1)"
  echo "Connecting network$i and network$j"
  $HERMES create channel "network$i" "network$j" --port-a transfer --port-b transfer
done < paths

