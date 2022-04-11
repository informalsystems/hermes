use serde::{Deserialize, Deserializer, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Meta {
    pub format: String,
    #[serde(rename = "format-description")]
    pub format_description: String,
    pub description: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct InformalTrace<S> {
    #[serde(rename = "#meta")]
    pub meta: Meta,
    pub vars: Vec<String>,
    pub states: Vec<S>,
}

#[derive(Debug, Serialize)]
pub struct Map<K, V>(pub Vec<(K, V)>);

impl<'de, K, V> Deserialize<'de> for Map<K, V>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Debug, Deserialize)]
        struct Meta<K, V> {
            #[serde(rename = "#map")]
            map: Vec<(K, V)>,
        }
        let s: Meta<_, _> = Deserialize::deserialize(deserializer)?;
        Ok(Self(s.map))
    }
}

#[derive(Debug, Serialize)]
pub struct Set<E>(pub Vec<E>);

impl<'de, E> Deserialize<'de> for Set<E>
where
    E: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Debug, Deserialize)]
        pub struct Meta<E> {
            #[serde(rename = "#set")]
            set: Vec<E>,
        }
        let s: Meta<_> = Deserialize::deserialize(deserializer)?;
        Ok(Self(s.set))
    }
}

mod test {
    use super::{Map, Set};

    #[test]
    fn test_empty_set() {
        let itf = r##"{ "#set": [] }"##;
        let s: Set<isize> = serde_json::from_str(itf).unwrap();
        assert!(s.0.is_empty());
    }

    #[test]
    fn test_set() {
        let itf = r##"{ "#set": [1,2,3] }"##;
        let s: Set<isize> = serde_json::from_str(itf).unwrap();
        assert_eq!(s.0, vec![1, 2, 3]);
    }

    #[test]
    fn test_empty_map() {
        let itf = r##"{ "#map": [ ] }"##;
        let m: Map<isize, isize> = serde_json::from_str(itf).unwrap();
        assert!(m.0.is_empty());
    }

    #[test]
    #[should_panic]
    fn test_singleton_map() {
        let itf = r##"{ "#map": [1, 11] }"##;
        let m: Map<isize, isize> = serde_json::from_str(itf).unwrap();
        assert_eq!(m.0, vec![(1, 11)]);
    }

    #[test]
    fn test_normal_map() {
        let itf = r##"{ "#map": [[1, 11], [2, 22]] }"##;
        let m: Map<isize, isize> = serde_json::from_str(itf).unwrap();
        assert_eq!(m.0, vec![(1, 11), (2, 22)]);
    }

    #[test]
    #[cfg(feature = "manual")]
    fn parse_itf() {
        use super::super::itf::InformalTrace;
        use super::super::state::State;

        let itf_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/spec/example/counterexample.itf.json"
        );

        let itf_json = std::fs::read_to_string(itf_path).expect("itf file does not exist");

        let t: InformalTrace<State> =
            serde_json::from_str(&itf_json).expect("deserialization error");

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
}
