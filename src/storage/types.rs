use crate::types::bytes::{Bytes32Target, U256Target};
use ethers_core::k256::U256;
use ethers_core::types::H256;
use plonky2_u32::gadgets::arithmetic_u32::U32Target;

#[derive(Clone, Debug)]
pub struct StorageKeyInputTarget {
    pub mapping_location: U32Target,
    pub map_key: Bytes32Target,
}

pub struct StorageKeyInput {
    pub mapping_location: u32,
    pub map_key: H256,
}
