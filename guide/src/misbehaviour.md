# Misbehaviour

## Table of Contents
<!-- toc -->

## Monitoring Misbehaviour and Evidence Submission
Use the `mishbehaviour` command to monitor the updates for a given client, detect certain types of misbehaviour and
submit evidence to the chain. If the evidence passed the on-chain validation, the client is frozen. Further packets
cannot be relayed using the frozen client.

```shell
USAGE:
    hermes misbehaviour <OPTIONS>

DESCRIPTION:
    Listen to client update IBC events and handles misbehaviour

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain where client updates are monitored for misbehaviour
    client_id                 identifier of the client to be monitored for misbehaviour
```

> This is an experimental feature.
