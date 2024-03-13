use crate::eth::mpt::BRANCH_NUM_ITEMS;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;

pub const fn max_leaf_lens(max_key_bytes: usize, max_value_bytes: usize) -> ([usize; 2], usize) {
    let max_encoded_path_bytes = max_key_bytes + 1;
    let max_encoded_path_rlp_bytes = max_rlp_encoding_len(max_encoded_path_bytes);
    let max_value_rlp_bytes = max_rlp_encoding_len(max_value_bytes);
    let max_field_bytes = [max_encoded_path_rlp_bytes, max_value_rlp_bytes];
    let max_leaf_bytes = max_rlp_encoding_len(max_encoded_path_rlp_bytes + max_value_rlp_bytes);
    (max_field_bytes, max_leaf_bytes)
}

pub const fn max_ext_lens(max_key_bytes: usize) -> ([usize; 2], usize) {
    let max_node_ref_bytes = 32;
    let max_encoded_path_bytes = max_key_bytes + 1;
    let max_encoded_path_rlp_bytes = max_rlp_encoding_len(max_encoded_path_bytes);
    let max_node_ref_rlp_bytes = max_rlp_encoding_len(max_node_ref_bytes);
    let max_field_bytes = [max_encoded_path_rlp_bytes, max_node_ref_rlp_bytes];
    let max_ext_bytes = max_rlp_encoding_len(max_encoded_path_rlp_bytes + max_node_ref_rlp_bytes);
    (max_field_bytes, max_ext_bytes)
}

pub const fn max_branch_lens(max_vt_bytes: usize) -> ([usize; BRANCH_NUM_ITEMS], usize) {
    let max_node_ref_bytes = 32;
    let max_node_ref_rlp_bytes = max_rlp_encoding_len(max_node_ref_bytes);
    let mut max_field_bytes = [max_node_ref_rlp_bytes; BRANCH_NUM_ITEMS];
    max_field_bytes[BRANCH_NUM_ITEMS - 1] = max_rlp_encoding_len(max_vt_bytes);
    let max_field_bytes_sum = 16 * max_node_ref_rlp_bytes + max_field_bytes[BRANCH_NUM_ITEMS - 1];
    let max_branch_bytes = max_rlp_encoding_len(max_field_bytes_sum);
    (max_field_bytes, max_branch_bytes)
}

/// RLP Module

/// Returns the number of bits needed to represent the value of `x`.
pub const fn bit_length(x: u64) -> usize {
    (u64::BITS - x.leading_zeros()) as usize
}

pub const fn max_rlp_len_len(max_len: usize) -> usize {
    if max_len > 55 {
        (bit_length(max_len as u64) + 7) / 8
    } else {
        0
    }
}

pub const fn max_rlp_encoding_len(payload_len: usize) -> usize {
    1 + max_rlp_len_len(payload_len) + payload_len
}

pub fn public_inputs_to_hex<F: RichField + Extendable<D>, const D: usize>(
    proof_public_inputs: Vec<F>,
) {
    let mut public_inputs = Vec::new();
    let mut pi_u8 = Vec::new();
    for i in proof_public_inputs.iter() {
        // transform Golidlocks Feilds to u32
        let mut tmp = i.to_canonical_u64();
        // transform u64 to big eidian u8

        for _ in 0..4 {
            pi_u8.push((tmp & 0xff) as u8);
            tmp >>= 8;
        }
        public_inputs.push(tmp);
    }
    // transform tmp_u8 to hex string, every u8 element is 2 hex char
    let mut public_inputs_hex = String::new();
    for i in pi_u8.iter() {
        public_inputs_hex.push_str(&format!("{:02x}", i));
    }
    println!("public inputs hex {:?}", public_inputs_hex);
}
