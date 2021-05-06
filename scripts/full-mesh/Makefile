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

network-start:
	docker compose -f docker-compose.gaiad.yml -p gaiad start

network-stop:
	docker compose -f docker-compose.gaiad.yml -p gaiad stop

network-down:
	docker compose -f docker-compose.gaiad.yml -p gaiad down || true

config-onchain: paths
	./3-create-onchain-config.sh
	./4-create-relayer-config.sh

# If this command fails with aliases, you need to upgrade Docker CLI to 1.0.14 or above.
relay-up:
	docker compose up -d

relay-down:
	docker compose down || true

clean: relay-down network-down
	@rm -rf gentxs network[0-9]* docker-compose.gaiad.yml docker-compose.yml paths .gaia .hermes
	@echo DONE

.PHONY: config-files network-up network-down config-onchain relay-up relay-start relay-stop relay-down clean all
