use ic_agent::identity::PemError;
use ic_agent::identity::Secp256k1Identity;
use std::path::PathBuf;

pub(crate) fn create_identity(pem_file: &PathBuf) -> Result<Secp256k1Identity, PemError> {
    Secp256k1Identity::from_pem_file(pem_file)
}

#[test]
fn test_create_identity() {
    let name = "default";
    let home_dir = dirs::home_dir().expect("Failed to get home directory");
    let pem_file_path = home_dir.join(std::path::Path::new(&format!(
        ".config/dfx/identity/{}/identity.pem",
        name
    )));
    let ret = create_identity(&pem_file_path);
    println!("ret = {:?}", ret);
}
