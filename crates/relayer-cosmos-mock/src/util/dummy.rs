use ibc::Signer;
use rand::RngCore;
use sha2::Digest;
use sha2::Sha256;

pub fn genesis_app_state() -> serde_json::Value {
    serde_json::json!({
      "cosmos12xpmzmfpf7tn57xg93rne2hc2q26lcfql5efws": {
        "basecoin": "0x1000000000",
        "othercoin": "0x1000000000",
        "samoleans": "0x1000000000"
      },
      "cosmos1t2e0nyjhwn3revunvf2uperhftvhzu4euuzva9": {
        "basecoin": "0x250",
        "othercoin": "0x5000"
      },
      "cosmos1uawm90a5xm36kjmaazv89nxmfr8s8cyzkjqytd": {
        "acidcoin": "0x500"
      },
      "cosmos1ny9epydqnr7ymqhmgfvlshp3485cuqlmt7vsmf": {},
      "cosmos1xwgdxu4ahd9eevtfnq5f7w4td3rqnph4llnngw": {
        "acidcoin": "0x500",
        "basecoin": "0x0",
        "othercoin": "0x100"
      },
      "cosmos1mac8xqhun2c3y0njptdmmh3vy8nfjmtm6vua9u": {
        "basecoin": "0x1000"
      },
      "cosmos1wkvwnez6fkjn63xaz7nzpm4zxcd9cetqmyh2y8": {
        "basecoin": "0x1"
      },
      "cosmos166vcha998g7tl8j8cq0kwa8rfvm68cqmj88cff": {
        "basecoin": "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
      },
      "cosmos1as9ap057eellftptlhyw5ajna7uaeewzkk6fnz": {
        "basecoin": "0x1000000000"
      }
    })
}

pub fn dummy_signer() -> Signer {
    Signer::from("cosmos000000000000000000000000000000000000000".to_string())
}

pub fn generate_rand_app_hash() -> Vec<u8> {
    let mut rng = rand::thread_rng();

    let mut data = vec![0u8; 32];

    rng.fill_bytes(&mut data);

    Sha256::digest(&data).to_vec()
}
