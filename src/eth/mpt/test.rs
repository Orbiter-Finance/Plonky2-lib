use ethers_core::types::EIP1186ProofResponse;
use std::fs::File;
use std::io::Read;

#[allow(dead_code)] // We allow dead_code since this is used in tests
pub(crate) fn read_fixture(filename: &str) -> EIP1186ProofResponse {
    let mut file = File::open(filename).unwrap();
    let mut context = String::new();
    file.read_to_string(&mut context).unwrap();

    let context: EIP1186ProofResponse = serde_json::from_str(context.as_str()).unwrap();
    context
}
