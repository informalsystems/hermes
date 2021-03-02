#!/usr/bin/env python3

import os

CFG = """
CONSTANTS
    ChainIds = {"chainA", "chainB"}
    MaxChainHeight = 4
    MaxClientsPerChain = 1
    MaxConnectionsPerChain = 1

INIT Init
NEXT Next

"""

tests = [
    "ICS02CreateOKTest",
    "ICS02UpdateOKTest",
    "ICS02ClientNotFoundTest",
    "ICS02HeaderVerificationFailureTest",
    "ICS03ConnectionOpenInitOKTest",
    "ICS03MissingClientTest",
    "ICS03ConnectionOpenTryOKTest",
    "ICS03InvalidConsensusHeightTest",
    "ICS03ConnectionNotFoundTest",
    "ICS03ConnectionMismatchTest",
    "ICS03MissingClientConsensusStateTest",
    "ICS03InvalidProofTest",
    "ICS03ConnectionOpenAckOKTest",
    "ICS03UninitializedConnectionTest",
    "ICS03ConnectionOpenConfirmOKTest",
]

for test in tests:
    # create IBCTests.cfg file
    with open("IBCTests.cfg", "w") as file:
        file.write(CFG + "INVARIANT " + test + "Neg")

    # run tlc-json
    print("> generating " + test)
    os.system("tlc-json IBCTests.tla")
    os.system("mv counterexample.json tests/" + test + ".json")
