import json
import toml
import sys
import os

def modify_genesis_json(genesis_path):
    # Load the genesis.json file
    with open(genesis_path, 'r') as file:
        genesis_data = json.load(file)

    # Modify the file according to the requirements
    genesis_data['app_state']['gov']['params']['max_deposit_period'] = "10s"
    genesis_data['app_state']['gov']['params']['voting_period'] = "10s"
    if "08-wasm" not in genesis_data['app_state']['ibc']['client_genesis']['params']['allowed_clients']:
        genesis_data['app_state']['ibc']['client_genesis']['params']['allowed_clients'].append("08-wasm")

    # Save the modified genesis.json file
    with open(genesis_path, 'w') as file:
        json.dump(genesis_data, file, indent=4)

def modify_config_toml(config_path):
    # Load the config.toml file
    with open(config_path, 'r') as file:
        config_data = toml.load(file)

    # Modify the file according to the requirements
    config_data['rpc']['max_body_bytes'] = 10001048576

    # Save the modified config.toml file
    with open(config_path, 'w') as file:
        toml.dump(config_data, file)

def main(chain_home):
    genesis_path = os.path.join(chain_home, 'config', 'genesis.json')
    config_path = os.path.join(chain_home, 'config', 'config.toml')

    if not os.path.exists(genesis_path) or not os.path.exists(config_path):
        print("Error: The specified paths do not exist.")
        sys.exit(1)

    modify_genesis_json(genesis_path)
    modify_config_toml(config_path)
    print("Modification completed successfully.")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <path_to_chain_home>")
        sys.exit(1)
    
    chain_home = sys.argv[1]
    main(chain_home)
