#![allow(dead_code)]

use tendermint::{block, consensus, evidence, public_key::Algorithm};

use crate::signer::Signer;

// Needed in mocks.
pub fn default_consensus_params() -> consensus::Params {
    consensus::Params {
        block: block::Size {
            max_bytes: 22020096,
            max_gas: -1, // Tendetmint-go also has TimeIotaMs: 1000, // 1s
        },
        evidence: evidence::Params {
            max_age_num_blocks: 100000,
            max_age_duration: evidence::Duration(std::time::Duration::new(48 * 3600, 0)),
            max_bytes: 0,
        },
        validator: consensus::params::ValidatorParams {
            pub_key_types: vec![Algorithm::Ed25519],
        },
        version: Some(consensus::params::VersionParams::default()),
    }
}

pub fn get_dummy_proof() -> Vec<u8> {
    // "Y29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIy"
    "CvEECjAKBGJhbmsSKAomCIjYAxIg2MEyyonbZButYnvSRkf2bPQg+nqA+Am1MeDxG6F4p1UKLwoDYWNjEigKJgiI2AMSIN2YHczeuXNvyetrSFQpkCcJzfB6PXVCw0i/XShMgPnIChEKB3VwZ3JhZGUSBgoECIjYAwovCgNnb3YSKAomCIjYAxIgYM0TfBli7KxhY4nWgDSDPykhUJwtKFql9RU5l86WinQKLwoDaWJjEigKJgiI2AMSIFp6aJASeInQKF8y824zjmgcFORN6M+ECbgFfJkobKs8CjAKBG1haW4SKAomCIjYAxIgsZzwmLQ7PH1UeZ/vCUSqlQmfgt3CGfoMgJLkUqKCv0EKMwoHc3Rha2luZxIoCiYIiNgDEiCiBZoBLyDGj5euy3n33ik+SpqYK9eB5xbI+iY8ycYVbwo0CghzbGFzaGluZxIoCiYIiNgDEiAJz3gEYuIhdensHU3b5qH5ons2quepd6EaRgCHXab6PQoyCgZzdXBwbHkSKAomCIjYAxIglWLA5/THPTiTxAlaLHOBYFIzEJTmKPznItUwAc8zD+AKEgoIZXZpZGVuY2USBgoECIjYAwowCgRtaW50EigKJgiI2AMSIMS8dZ1j8F6JVVv+hB1rHBZC+gIFJxHan2hM8qDC64n/CjIKBnBhcmFtcxIoCiYIiNgDEiB8VIzExUHX+SvHZFz/P9NM9THnw/gTDDLVReuZX8htLgo4CgxkaXN0cmlidXRpb24SKAomCIjYAxIg3u/Nd4L+8LT8OXJCh14o8PHIJ/GLQwsmE7KYIl1GdSYKEgoIdHJhbnNmZXISBgoECIjYAw=="
        .as_bytes()
        .to_vec()
}

pub fn get_dummy_account_id() -> Signer {
    "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C".parse().unwrap()
}

pub fn get_dummy_bech32_account() -> String {
    "cosmos1wxeyh7zgn4tctjzs0vtqpc6p5cxq5t2muzl7ng".to_string()
}
