use ethers_core::types::H256;
use serde::{Deserialize, Serialize};

use crate::hash::HashTarget;
use crate::nonnative::biguint::BigUintTarget;
use crate::types::bytes::{Bytes32Target, U32ArrayTarget};

#[derive(Clone, Debug, Serialize, Deserialize, Hash)]
pub struct PathBytes(pub Vec<u8>);

impl<T: AsRef<[u8]>> From<&T> for PathBytes {
    fn from(value: &T) -> Self {
        Self(value.as_ref().to_vec())
    }
}

impl From<Vec<u8>> for PathBytes {
    fn from(value: Vec<u8>) -> Self {
        Self(value)
    }
}

impl From<H256> for PathBytes {
    fn from(value: H256) -> Self {
        Self(value.0.to_vec())
    }
}

impl AsRef<[u8]> for PathBytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Input

#[derive(Clone, Debug, Hash, Serialize, Deserialize)]
pub struct MPTInput {
    // claim specification: (path, value)
    /// A Merkle-Patricia Trie is a mapping `path => value`
    ///
    /// As an example, the MPT state trie of Ethereum has
    /// `path = keccak256(address) => value = rlp(account)`
    pub path: PathBytes,
    pub value: Vec<u8>,
    pub root_hash: H256,

    /// Inclusion proofs will always end in a terminal node: we extract this terminal node in cases where it was originally embedded inside the last branch node.
    pub proof: Vec<Vec<u8>>,

    pub slot_is_empty: bool,

    pub value_max_byte_len: usize,
    pub max_depth: usize,
    pub max_key_byte_len: usize,
    pub key_byte_len: Option<usize>,
}

pub type MPTHash = HashTarget;

const MAX_DEPTH: usize = 17;
pub(crate) const ENCODING_LEN: usize = 600;

#[derive(Clone, Debug)]
pub struct MPTProofTarget<const DEPTH: usize> {
    // claim specification: (key, value)
    /// The key bytes, fixed length, resized to `KECCAK256_R/BITS_LEN`
    pub key_bytes: BigUintTarget,
    /// The RLP encoded `value` as bytes, variable length, resized to `KECCAK256_R/BITS_LEN`
    pub value_bytes: BigUintTarget,
    pub root_hash_bytes: Bytes32Target,

    // proof specification
    /// This is proof, resized to max_depth - 1.
    pub proof: [BigUintTarget; DEPTH],

    /// The non-leaf nodes of the mpt proof, resized to `max_depth - 1` nodes.
    pub len_nodes: U32ArrayTarget<DEPTH>,

    /// The maximum byte length of the key
    pub max_key_byte_len: usize,

    pub encode_len: usize,
}
