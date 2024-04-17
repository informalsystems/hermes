import subprocess
import json
import sys
import time

def run_command(command):
    result = subprocess.run(command, shell=True, capture_output=True, text=True)
    if result.returncode != 0:
        return {}
    return json.loads(result.stdout)

def get_last_proposal_id(chain_home, node):
    while True:
        command = f"simd query gov proposals --home {chain_home} --node {node} --output json"
        output = run_command(command)
        proposals = output.get("proposals")
        if not proposals:
            print("No proposals found. Waiting...")
            time.sleep(2)
            continue

        deposit_period_proposals = [proposal for proposal in proposals if proposal.get("status") == "PROPOSAL_STATUS_DEPOSIT_PERIOD"]
        if deposit_period_proposals:
            last_proposal_id = max(int(proposal["id"]) for proposal in deposit_period_proposals)
            return str(last_proposal_id)
        else:
            print("No proposals in DEPOSIT_PERIOD found. Waiting...")
            time.sleep(2)

def check_proposal_status(chain_home, node, proposal_id, expected_status, max_tries=10):
    tries = 0
    while tries < max_tries:
        command = f"simd query gov proposal {proposal_id} --home {chain_home} --node {node} --output json"
        output = run_command(command)
        proposal_status = output.get("status")
        if proposal_status == expected_status:
            print(f"Proposal status is now {proposal_status}. Exiting loop.")
            return
        else:
            print(f"Proposal status is {proposal_status}. Continuing to check...")
        tries += 1
        time.sleep(2)
    
    print("[ERROR] Failed due to an issue with the proposal")
    sys.exit(1)

def main(chain_id, node, signer):
    chain_home = f"$HOME/.gm/{chain_id}"
    contract = "./ibc_client_tendermint_cw.wasm"

    # Store code
    print('Storing the IBC Wasm client contract on the chain...')
    store_code_command = (f"simd tx ibc-wasm store-code {contract} --title tmp --summary tmp --fees 1000016stake "
                          f"--deposit 200000stake --home {chain_home} --node {node} --from {signer} --chain-id {chain_id} "
                          f"--keyring-backend test --gas auto -y --output json")
    run_command(store_code_command)
    print('=> Code stored successfully')

    # Fetch the last proposal ID
    print('Fetching the proposal ID...')
    proposal_id = get_last_proposal_id(chain_home, node)
    print(f"=> Proposal ID: {proposal_id}")

    # Check for PROPOSAL_STATUS_DEPOSIT_PERIOD
    check_proposal_status(chain_home, node, proposal_id, "PROPOSAL_STATUS_DEPOSIT_PERIOD")

    # Deposit
    print('Depositing 100000000stake on the proposal...')
    deposit_command = (f"simd tx gov deposit {proposal_id} 100000000stake --home {chain_home} --node {node} "
                       f"--from {signer} --chain-id {chain_id} --keyring-backend test --gas auto -y --output json")
    run_command(deposit_command)
    print('=> Deposit successful')

    # Check for PROPOSAL_STATUS_VOTING_PERIOD
    check_proposal_status(chain_home, node, proposal_id, "PROPOSAL_STATUS_VOTING_PERIOD")

    # Vote
    print('Voting YES on the proposal...')
    vote_command = (f"simd tx gov vote {proposal_id} yes --home {chain_home} --node {node} "
                    f"--from {signer} --chain-id {chain_id} --keyring-backend test --gas auto -y --output json")
    run_command(vote_command)
    print('=> Vote successful')

    # Check for PROPOSAL_STATUS_PASSED
    check_proposal_status(chain_home, node, proposal_id, "PROPOSAL_STATUS_PASSED")

    print('SUCCESS: Contract installed successfully')

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python script.py <CHAIN_ID> <NODE> <SIGNER>")
        sys.exit(1)

    chain_id, node, signer = sys.argv[1], sys.argv[2], sys.argv[3]
    main(chain_id, node, signer)
