DESCRIPTION:
Send an IBC upgrade plan

USAGE:
    hermes tx upgrade-chain [OPTIONS] --reference-chain <REFERENCE_CHAIN_ID> --host-chain <HOST_CHAIN_ID> --host-client <HOST_CLIENT_ID> --amount <AMOUNT> --height-offset <HEIGHT_OFFSET> --gov-account <GOV_ACCOUNT>

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

        --gov-account <GOV_ACCOUNT>
            Authority account used to sign upgrade proposal

        --height-offset <HEIGHT_OFFSET>
            Upgrade height offset in number of blocks since current

        --host-chain <HOST_CHAIN_ID>
            Identifier of the host chain

        --host-client <HOST_CLIENT_ID>
            Identifier of the client on the host chain from which the plan is created

        --reference-chain <REFERENCE_CHAIN_ID>
            Identifier of the chain to upgrade
