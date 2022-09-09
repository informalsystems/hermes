DESCRIPTION:
Send an IBC upgrade plan

USAGE:
    hermes tx upgrade-chain [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-client <SRC_CLIENT_ID> --amount <AMOUNT> --height-offset <HEIGHT_OFFSET>

OPTIONS:
        --denom <DENOM>
            Denomination for the deposit (default: 'stake')

    -h, --help
            Print help information

        --new-chain <CHAIN_ID>
            New chain identifier to assign to the upgrading chain (optional)

        --new-unbonding <UNBONDING_PERIOD>
            New unbonding period to assign to the upgrading chain, in seconds (optional)

        --upgrade-name <UPGRADE_NAME>
            A string to name the upgrade proposal plan (default: 'plan')

REQUIRED:
        --amount <AMOUNT>
            Amount of stake

        --dst-chain <DST_CHAIN_ID>
            Identifier of the chain to upgrade

        --height-offset <HEIGHT_OFFSET>
            Upgrade height offset in number of blocks since current

        --src-chain <SRC_CHAIN_ID>
            Identifier of the host chain

        --src-client <SRC_CLIENT_ID>
            Identifier of the client on the host chain from which the plan is created
