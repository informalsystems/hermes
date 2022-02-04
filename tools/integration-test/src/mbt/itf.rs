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
pub struct Map<K, V>(Vec<(K, V)>);

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
        #[serde(untagged)]
        enum CustVec<K, V> {
            One((K, V)),
            Multi(Vec<(K, V)>),
        }
        #[derive(Debug, Deserialize)]
        struct Meta<K, V> {
            #[serde(rename = "#map")]
            map: CustVec<K, V>,
        }
        let s: Meta<_, _> = Deserialize::deserialize(deserializer)?;
        Ok(match s.map {
            CustVec::Multi(v) => Self(v),
            CustVec::One(e) => Self(vec![e]),
        })
    }
}

#[derive(Debug, Serialize)]
pub struct Set<E>(Vec<E>);

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
    fn test_set() {
        let itf = r##"{ "#set": [1,2,3] }"##;
        let s: Set<isize> = serde_json::from_str(itf).unwrap();
        assert_eq!(s.0, vec![1, 2, 3]);
    }

    #[test]
    fn test_empty_map() {
        let itf = r##"{ "#map": [ ] }"##;
        let m: Map<isize, isize> = serde_json::from_str(itf).unwrap();
        assert_eq!(m.0, vec![]);
    }

    #[test]
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
}
