use super::state::State;

#[test]
fn it_works() {
    let tla_path = "spec/main.tla";
    let cfg_path = "spec/main.cfg";

    let runtime = modelator::ModelatorRuntime::default();
    let traces = runtime.traces(tla_path, cfg_path).expect("error");

    for (test_name, result) in traces.iter() {
        let trace: Vec<Result<State, _>> = result
            .as_ref()
            .unwrap()
            .get(0)
            .unwrap()
            .clone()
            .into_iter()
            .map(serde_json::from_value)
            .collect();

        println!("{test_name}, {trace:?}",);
    }
}
