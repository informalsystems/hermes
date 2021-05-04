#!/bin/sh

##############################
## Script setup
##############################

# Fail if there are any errors
set -eu

# Run in a subfolder, not in your $HOME (safeguard against accidental .hermes-deletions)
test "$HOME" != "$(pwd)"

EXPECTED_HERMES_VERSION=0.2.0
DOCKER_IMAGE="informaldev/hermes:${EXPECTED_HERMES_VERSION}"

##############################
## Create docker-compose.yml (set of hermes relayers)
##############################

cat <<EOF > docker-compose.yml
services:
EOF

while read -r line;
do
  VALID="$(echo "$line" | grep '^[ ]*[0-9]\+[ ]\+[0-9]\+[ ]*$' || echo "")"
  test -n "$VALID" || continue
  i="$(echo "$line" | grep -o '[0-9]\+' | head -1)"
  j="$(echo "$line" | grep -o '[0-9]\+' | tail -1)"

  cat <<EOF >> docker-compose.yml
  hermes-${i}-${j}:
    container_name: hermes-${i}-${j}
    network_mode: "host"
    image: "$DOCKER_IMAGE"
    entrypoint: "/usr/bin/hermes"
    command: start network$i network$j -p transfer -c channel-0
    volumes:
      - $(pwd)/.hermes:/home/hermes/.hermes
EOF

done < paths

