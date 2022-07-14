# Continous Integration for ibc-rs

This folder contains the files required to run the End to end testing in [Github Actions](https://github.com/informalsystems/ibc-rs/actions)

## End to end (e2e) testing

The [End to end (e2e) testing workflow](https://github.com/informalsystems/ibc-rs/actions?query=workflow%3A%22End+to+End+testing%22) spins up two `gaia` chains (`ibc-0` and `ibc-1`) in Docker containers and one container that runs the relayer. There's a script that configures the relayer (e.g. configure light clients and add keys) and runs transactions and queries. A successful run of this script ensures that the relayer is working properly with two chains that support `IBC`.

### Testing Ethermint-based networks
At this moment, the automated E2E workflow does not spin up a network with the (post-Stargate) Ethermint module. In the meantime, you can test it manually by following one of the resources below:

- [the official documentation on ethermint.dev](https://docs.ethermint.zone/quickstart/run_node.html)
- [using the tweaked E2E scripts from the Injective's fork](https://github.com/InjectiveLabs/ibc-rs/commit/669535617a6e45be9916387e292d45a77e7d23d2)
- [using the nix-based integration test scripts in the Cronos project](https://github.com/crypto-org-chain/cronos#quitck-start)

### Running an End to end (e2e) test locally

If you want to run the end to end test locally, you will need [Docker](https://www.docker.com/) installed on your machine.

Follow these steps to run the e2e test locally:

__Note__: This assumes you are running this the first time, if not, please ensure you follow the steps to [clean up the containers](#cleaning-up) before running it again.

1. Clone the `ibc-rs` repo.

2. Go into the repository folder:

    `cd ibc-rs`

3. Build the current up-to-date relayer container image. Make sure you have a
   copy of the `hermes` binary in the root of the repo, as the docker script
   expects this. If you don't, you can run `cp ./target/debug/hermes .`. This
   command might take a few minutes since it will do a fresh compile and build
   of all modules:

    `docker-compose -f ci/docker-compose-gaia-current.yml build relayer`

> Note: If you're looking to test on a legacy version of gaia, run:
> `docker-compose -f ci/docker-compose-gaia-legacy.yml build relayer`.
> You'll use the `docker-compose-gaia-legacy.yml` configuration instead of
> `docker-compose-gaia-current.yml` in all cases.

4. Run all the containers (two containers, one for each chain and one for the relayer)

   `docker-compose -f ci/docker-compose-gaia-current.yml up -d ibc-0 ibc-1 relayer`

    If everything is successful you should see among the output something
    similar to this:
    ```shell
    Network ci_relaynet  Created
    Container ibc-1      Started
    Container ibc-0      Started
    Container relayer    Started
    ```

    If you want to ensure they are all running properly you can use the command:

    `docker-compose -f ci/docker-compose-gaia-current.yml ps`

    You should see the message below. Please ensure all containers are in a `running` state.
    ```shell

    ibc-0     "/chain/gaia/run-gaia..."   ibc-0         running
    ibc-1     "/chain/gaia/run-gaia..."   ibc-1         running
    relayer   "/bin/sh"                   relayer       running
    ```

    __Note__: If this is the first time you're running this command, the `informaldev/ibc-0:[RELEASE TAG]` and `informaldev/ibc-1:[RELEASE TAG]` container images will be pulled from the Docker Hub. For instructions on how to update these images in Docker Hub please see the [upgrading the release](#upgrading-chains) section.


5. Run the command below to execute the relayer end to end (e2e) test. This command will execute the `e2e.sh` on the relayer container. The script will configure the light clients for both chains, add the private keys for both chains and run transactions on both chains (e.g. create client transaction).

    `docker exec relayer /bin/sh -c /relayer/e2e.sh`

    If the script runs sucessfully you should see an output similar to this one:
```shell
=================================================================================================================
                                              INITIALIZE
=================================================================================================================
-----------------------------------------------------------------------------------------------------------------
Show relayer version
-----------------------------------------------------------------------------------------------------------------
relayer-cli 0.2.0
-----------------------------------------------------------------------------------------------------------------
Setting up chains
-----------------------------------------------------------------------------------------------------------------
Config: /relayer/simple_config.toml
  Chain: ibc-0
    creating chain store folder: [/data/ibc-0]
  Chain: ibc-1 [/data/ibc-1]
    creating chain store folder: [/data/ibc-1]
Waiting 20 seconds for chains to generate blocks...
=================================================================================================================
                                            CONFIGURATION
=================================================================================================================
-----------------------------------------------------------------------------------------------------------------
Add keys for chains
-----------------------------------------------------------------------------------------------------------------
key add result:  "Added key testkey (cosmos1tc3vcuxyyac0dmayf887v95tdg7qpyql48w7gj) on ibc-0 chain"
key add result:  "Added key testkey (cosmos1zv3etpuk4n7p54r8fhsct0qys8eqf5zqw4pqp5) on ibc-1 chain"
-----------------------------------------------------------------------------------------------------------------
Set the primary peers for clients on each chain
-----------------------------------------------------------------------------------------------------------------
Executing: hermes -c /relayer/simple_config.toml light add tcp://ibc-0:26657 -c ibc-0 -s /data/ibc-0 -p -y -f
     Success Added light client:
  chain id: ibc-0
  address:  tcp://ibc-0:26657
  peer id:  DF766B47325BE49E27F9DF325327853AAFB5BBCA
  height:   731
  hash:     22639F0B84C0E95D51AB70D900E7BC0CBFBDF642F3F945093FF7AEB8120CC8DC
  primary:  true
-----------------------------------------------------------------------------------------------------------------
Executing: hermes -c /relayer/simple_config.toml light add tcp://ibc-1:26657 -c ibc-1 -s /data/ibc-1 -p -y -f
     Success Added light client:
  chain id: ibc-1
  address:  tcp://ibc-1:26657
  peer id:  B7A2809AA8AA825225D618DDD5200AB9BA236797
  height:   733
  hash:     D5C190747A1A0805C4840FBF66EC3339E0C30520359EF36553508DBD775A6EEF
  primary:  true
-----------------------------------------------------------------------------------------------------------------
Set the secondary peers for clients on each chain
-----------------------------------------------------------------------------------------------------------------
Executing: hermes -c /relayer/simple_config.toml light add tcp://ibc-0:26657 -c ibc-0 -s /data/ibc-0 --peer-id 17D46D8C1576A79203A6733F63B2C9B7235DD559 -y
     Success Added light client:
  chain id: ibc-0
  address:  tcp://ibc-0:26657
  peer id:  17D46D8C1576A79203A6733F63B2C9B7235DD559
  height:   735
  hash:     463691EED61772C333D38C5DC5F267946341F98ADE8EF9FBBE501A96022E5F1A
  primary:  false
-----------------------------------------------------------------------------------------------------------------
Executing: hermes -c /relayer/simple_config.toml light add tcp://ibc-1:26657 -c ibc-1 -s /data/ibc-1 --peer-id A885BB3D3DFF6101188B462466AE926E7A6CD51E -y
     Success Added light client:
  chain id: ibc-1
  address:  tcp://ibc-1:26657
  peer id:  A885BB3D3DFF6101188B462466AE926E7A6CD51E
  height:   737
  hash:     5377D2FDCD1886129AF32AABFDFC4C80112B2465F49814E91C25FD325DE54DCC
  primary:  false
=================================================================================================================
                                             CLIENTS
=================================================================================================================
-----------------------------------------------------------------------------------------------------------------
Create client transactions
-----------------------------------------------------------------------------------------------------------------
Creating ibc-1 client on chain ibc-0
Message CreateClient for source chain: ChainId { id: "ibc-1", version: 1 }, on destination chain: ChainId { id: "ibc-0", version: 0 }
Jan 21 18:46:57.259  INFO relayer::event::monitor: running listener chain.id=ibc-1
Jan 21 18:46:57.278  INFO relayer::event::monitor: running listener chain.id=ibc-0
{"status":"success","result":[{"CreateClient":{"client_id":"07-tendermint-0","client_type":"Tendermint","consensus_height":{"revision_height":739,"revision_number":1},"height":"1"}}]}
-----------------------------------------------------------------------------------------------------------------
Creating ibc-0 client on chain ibc-1
Message CreateClient for source chain: ChainId { id: "ibc-0", version: 0 }, on destination chain: ChainId { id: "ibc-1", version: 1 }
Jan 21 18:46:58.299  INFO relayer::event::monitor: running listener chain.id=ibc-0
Jan 21 18:46:58.324  INFO relayer::event::monitor: running listener chain.id=ibc-1
{"status":"success","result":[{"CreateClient":{"client_id":"07-tendermint-0","client_type":"Tendermint","consensus_height":{"revision_height":740,"revision_number":0},"height":"1"}}]}
```

### [Cleaning up](#cleaning-up)

In order to clear up the testing environment and stop the containers you can run the command below

`docker-compose -f ci/docker-compose-gaia-current.yml down`

If the command executes successfully you should see the message below:

```shell
Container relayer    Removed
Container ibc-1      Removed
Container ibc-0      Removed
Network ci_relaynet  Removed
```

### [Upgrading the gaia chains release and generating new container images](#upgrading-chains)

The repository stores the files used to configure and build the chains for the containers. For example, the files for a `gaia` chain release `v5.0.0` can be seen [here](./chains/gaia)

> Note: Please ensure you have gaiad installed on your machine and it matches the version that you're trying to upgrade.
> You can check by running `gaiad version` in your machine.
>
> If you need to upgrade your local `gaiad` binary, you can follow the steps
> listed in the Cosmos Hub documentation on [installing the binary](https://hub.cosmos.network/main/getting-started/installation.html).

If you need to generate configuration files for a new gaia release and new containers, please follow the steps below:

1. Move into the `ci` folder

    `cd ci`


2. Open the `build-ibc-chains.sh` file and change the release. Just replace the value for the `GAIA_BRANCH` parameter. For example to set it to release `v5.0.0` use:
    `GAIA_BRANCH="v5.0.0"`


3. Run the `build-ibc-chains.sh` script:

    `./build-ibc-chains.sh`


__Note__: This will generate the files for the chains in the `/ci/chains/gaia` folder and build the Docker containers. At the end of the script it will ask if you want to push these new images to Docker Hub. In order to do so you need to have Docker login configured on your machine with permissions to push the container. If you don't want to push them (just have them built locally) just cancel the script execution (by hitting `CTRL+C`)


4. Committing the release files. **You have to** add the new chain files generated to the ibc-rs repository, just `git commit` the files, otherwise the CI might fail because private keys don't match.


5. Update the release for Docker Compose. If this new release should be the default release for running the end to end (e2e) test you need to update the release version in the `docker-compose.yml` file in the `ci` folder of the repository. Open the file and change the release version in all the places required (image name and RELEASE variables. For example, if current release is `v4.0.0` and the new one is `v5.0.0` just do a find and replace with these two values.

Change the version in the image for ibc-0 and ibc-1 services:

   ```
   image: "informaldev/ibc-0:v4.0.0"
   ```

And in the relayer service:

   ```
      args:
        RELEASE: v4.0.0
   ```

6. Update the CI workflow

There are currently two CI workflows, for running the E2E tests against two versions of gaiad:
   - legacy release: `.github\workflows\e2e-gaia-legacy-release.yaml`, and
   - current release: `.github\workflows\e2e-gaia-current-release.yaml`.

Depending on which of the two setups you have upgraded at the prior steps, change the `name` key in the corresponding workflow file to match with the version of the upgraded gaia used, e.g.:

`name: End to End testing (Gaia - v6.0.0)`
