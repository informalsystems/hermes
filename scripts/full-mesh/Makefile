# Number of nodes
N?=5

all: setup-network setup-relay

setup-network: config-files network-up
setup-relay: config-onchain relay-up

config-files:
	./1-create-network-config.sh $(N)
	./2-create-hermes-config.sh $(N)

network-up:
	docker compose -f docker-compose.gaiad.yml -p gaiad up -d
	sleep 5

network-down:
	docker compose -f docker-compose.gaiad.yml -p gaiad down || true

config-onchain: paths
	./3-create-onchain-config.sh
	./4-create-relayer-config.sh


# Todo: move the relay-* commands to `docker compose` when this is fixed:
#  https://github.com/docker/compose-cli/issues/1637
# Use docker-compose until then.
relay-up:
	docker-compose up -d

relay-start:
	docker-compose start

relay-stop:
	docker-compose stop

relay-down:
	docker-compose down || true

clean: relay-down network-down
	@rm -rf gentxs network[0-9]* docker-compose.gaiad.yml docker-compose.yml paths .gaia .hermes
	@echo DONE

.PHONY: config-files network-up network-down config-onchain relay-up relay-start relay-stop relay-down clean all
