use super::itf::InformalTrace;
use super::state::State;

#[test]
fn parse_itf() {
    let itf_path = "spec/run/counterexample.itf.json";

    let itf_json = std::fs::read_to_string(itf_path).expect("itf file does not exist. did you run `apalache check --inv=Invariant --run-dir=run main.tla` inside `spec/`?");

    let t: InformalTrace<State> = serde_json::from_str(&itf_json).expect("deserialization error");

    for state in t.states {
        println!(
            "action: {}",
            serde_json::to_string_pretty(&state.action).unwrap()
        );
        println!(
            "outcome: {}",
            serde_json::to_string_pretty(&state.outcome).unwrap()
        );
        println!(
            "chains: {}",
            serde_json::to_string_pretty(&state.chains).unwrap()
        );
    }
}
