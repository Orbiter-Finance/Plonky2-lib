use std::io::Read;

use hex::FromHex;
use itertools::Itertools;
use lazy_static::lazy_static;
use num::traits::ToBytes;
use num::{BigUint, FromPrimitive};
use plonky2::field::extension::Extendable;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, Witness};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, KeccakGoldilocksConfig, PoseidonGoldilocksConfig};
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};
use plonky2_u32::witness::WitnessU32;

use crate::eth::mpt::types::{MPTHash, MPTInput, MPTProofTarget, ENCODING_LEN};
use crate::eth::mpt::utils::{max_branch_lens, public_inputs_to_hex};
use crate::hash::keccak256::{CircuitBuilderHashKeccak, WitnessHashKeccak, KECCAK256_R};
use crate::hash::{CircuitBuilderHash, WitnessHash};
use crate::nonnative::biguint::{BigUintTarget, CircuitBuilderBiguint, WitnessBigUint};
use crate::types::bytes::{
    ByteTarget, Bytes32ArrayTarget, Bytes32Target, BytesTarget, WitnessBytes,
};
use crate::types::bytes::{CircuitBuilderBytes, Nibbles, U32ArrayTarget};
use crate::types::math::less_than_equal_u32;

mod rlc;
mod test;
mod types;
pub mod utils;

const PREFIX_EXTENSION_EVEN: u8 = 0;
const PREFIX_EXTENSION_ODD: u8 = 1;
const PREFIX_LEAF_EVEN: u8 = 2;
const PREFIX_LEAF_ODD: u8 = 3;

pub const BRANCH_NUM_ITEMS: usize = 17;
pub const MAX_BRANCH_ENCODING_BYTES: usize = max_branch_lens(1).1;

lazy_static! {
    static ref DUMMY_BRANCH: Vec<u8> = Vec::from_hex("d18080808080808080808080808080808080").unwrap();
    static ref DUMMY_EXT: Vec<u8> = Vec::from_hex(
            "e21ba00000000000000000000000000000000000000000000000000000000000000000").unwrap();
    /// rlp(["", 0x0])
    static ref NULL_LEAF: Vec<u8> = Vec::from_hex(
            "c3818000").unwrap();
    /// keccak(rlp("")) = keccak(0x80)
    pub static ref KECCAK_RLP_EMPTY_STRING: Vec<u8> = Vec::from_hex(
            "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").unwrap();
    static ref RLP_EMPTY_STRING: Vec<u8> = Vec::from_hex(
            "80").unwrap();
}

pub trait CircuitBuilderMPT<F: RichField + Extendable<D>, const D: usize> {
    // fn build_input(&mut self, input: MPTInput) -> MPTProof;

    /// When one node is referenced inside another node, what is included is H(rlp.encode(x)), where H(x) = keccak256(x) if len(x) >= 32 else x and rlp.encode is the RLP encoding function.
    ///
    /// Assumes that `bytes` is non-empty.
    fn mpt_hash(&mut self, bytes: &BigUintTarget, len: U32Target) -> MPTHash;

    fn test_mpt_hash(&mut self, input: &TestInputTarget) -> MPTHash;

    fn test_mpt_hash_l(&mut self, bytes: &BigUintTarget) -> MPTHash;

    fn add_virtual_mpt_proof_target<const DEPTH: usize>(
        &mut self,
        max_depth: usize,
        keccak256_r: usize,
    ) -> MPTProofTarget<DEPTH>;

    fn parse_mpt_inclusion_proof<const DEPTH: usize>(&mut self, proof: &MPTProofTarget<DEPTH>);
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderMPT<F, D>
    for CircuitBuilder<F, D>
{
    fn mpt_hash(&mut self, bytes: &BigUintTarget, len: U32Target) -> MPTHash {
        let hash = self.add_virtual_hash_input_target(4, KECCAK256_R);

        let out = self.hash_keccak256(&hash);
        self.connect_hash_input(&hash, bytes, 0);

        MPTHash {
            input_bits: hash.input_bits,
            input: hash.input,
            output: out,
            blocks: hash.blocks,
        }
    }

    fn test_mpt_hash(&mut self, input: &TestInputTarget) -> (MPTHash) {
        self.test_mpt_hash_l(&input.value_bytes)
    }

    fn test_mpt_hash_l(&mut self, bytes: &BigUintTarget) -> (MPTHash) {
        let hash = self.add_virtual_hash_input_target(4, KECCAK256_R);

        let out = self.hash_keccak256(&hash);
        self.connect_hash_input(&hash, bytes, 0);

        MPTHash {
            input_bits: hash.input_bits,
            input: hash.input,
            output: out,
            blocks: hash.blocks,
        }
    }

    fn add_virtual_mpt_proof_target<const DEPTH: usize>(
        &mut self,
        max_depth: usize,
        keccak256_r: usize, //KECCAK256_R
    ) -> MPTProofTarget<DEPTH> {
        const BITS_LEN: usize = 8;
        let root_hash_bytes = self.add_virtual_bytes32_target();
        let key_bytes = self.add_virtual_biguint_target(keccak256_r / BITS_LEN);
        let value_bytes = self.add_virtual_biguint_target(keccak256_r / BITS_LEN);
        let len_nodes = self.add_virtual_u32_array_target::<DEPTH>();
        let proof: Vec<_> = (0..DEPTH)
            .map(|_| self.add_virtual_biguint_target(keccak256_r / BITS_LEN))
            .collect();
        let proof: [BigUintTarget; DEPTH] = proof.try_into().unwrap();

        MPTProofTarget {
            key_bytes,
            root_hash_bytes,
            proof,
            len_nodes,
            value_bytes,
            max_key_byte_len: 0,
            encode_len: 0,
        }
    }

    // Maximum size of list element is 32
    fn parse_mpt_inclusion_proof<const DEPTH: usize>(&mut self, proof: &MPTProofTarget<DEPTH>) {
        const ELEMENT_LEN: usize = 32; // Maximum size of list element
        const LIST_LEN: usize = 17; // Maximum length of the list for each proof element

        let tree_radix = self.constant(F::from_canonical_u32(16));
        let branch_node_length = self.constant(F::from_canonical_u32(17));
        let leaf_or_extension_node_length = self.constant(F::from_canonical_u32(2));
        let prefix_leaf_even = ByteTarget::from_u8(self, PREFIX_LEAF_EVEN);
        let prefix_leaf_odd = ByteTarget::from_u8(self, PREFIX_LEAF_ODD);
        let prefix_extension_even = ByteTarget::from_u8(self, PREFIX_EXTENSION_EVEN);
        let prefix_extension_odd = ByteTarget::from_u8(self, PREFIX_EXTENSION_ODD);
        let one = self.one();
        let two = self.two();
        let const_64 = self.constant(F::from_canonical_u32(64));
        let const_32 = self.constant_u32(32);
        let const_128 = self.constant_u32(128);

        let mut current_key_idx = self.zero();
        let mut finished = self._false();

        let mut current_node_id = proof.root_hash_bytes.clone();

        // Todo: move to key_frag function

        // s
        let hash_key = self.mpt_hash(&proof.key_bytes, U32Target::default());
        let key_path: BytesTarget<64> = Bytes32Target::from_biguint_target(self, hash_key.output)
            .as_bytes()
            .to_vec()
            .to_nibbles(self)
            .into();
        // e

        for i in 0..DEPTH {
            let current_node = proof.proof[i].clone();
            let current_node_hash = self.mpt_hash(&current_node, U32Target::default());
            let current_node_hash =
                Bytes32Target::from_biguint_target(self, current_node_hash.output);
            let current_node = BytesTarget::<ENCODING_LEN>::from_biguint_target(self, current_node);

            if i == 0 {
                self.assert_bytes32_is_equal(current_node_hash, proof.root_hash_bytes);
            } else {
                let current_node: Bytes32Target = current_node.as_slice()[0..32].to_vec().into();
                let first_32_bytes_eq = current_node.is_equal(self, current_node_id);
                let hash_eq = current_node_hash.is_equal(self, current_node_id);
                let node_len_le_32 =
                    less_than_equal_u32(self, proof.len_nodes.targets()[i], const_32);
                let case_len_le_32 = self.and(node_len_le_32, first_32_bytes_eq);
                let inter = self.not(node_len_le_32);
                let case_len_gt_32 = self.and(inter, hash_eq);
                let equality_fulfilled = self.or(case_len_le_32, case_len_gt_32);
                let checked_equality = self.or(equality_fulfilled, finished);
                let t = self._true();
                self.is_equal(checked_equality.target, t.target);
            }

            // let (decoded_list, decoded_element_lens, len_decoded_list) = self
            //     .decode_element_as_list::<ENCODING_LEN, LIST_LEN, ELEMENT_LEN>(
            //         current_node,
            //         proof.len_nodes.targets()[i],
            //         finished,
            //     );

            let decoded_list = self.add_virtual_bytes32_array_target::<LIST_LEN>();

            let decoded_element_lens = U32ArrayTarget::<LIST_LEN>::new();
            let len_decoded_list = Target::default();
            let is_branch = self.is_equal(len_decoded_list, branch_node_length);
            let is_leaf = self.is_equal(len_decoded_list, leaf_or_extension_node_length);
            let key_terminated = self.is_equal(current_key_idx, const_64);
            let path: Vec<ByteTarget> = decoded_list.as_slice()[0]
                .as_bytes()
                .to_vec()
                .to_nibbles(self);
            let prefix = path[0];
            let prefix_leaf_even = prefix.is_equal(self, prefix_leaf_even);
            let prefix_leaf_odd = prefix.is_equal(self, prefix_leaf_odd);
            let prefix_extension_even = prefix.is_equal(self, prefix_extension_even);
            let prefix_extension_odd = prefix.is_equal(self, prefix_extension_odd);

            let offset_even = self.mul(prefix_extension_even.target, two);
            let offset_odd = self.mul(prefix_extension_odd.target, one);
            let offset = self.add(offset_even, offset_odd);
            let branch_key = key_path.select_array(self, current_key_idx);
            let branch_key_target = branch_key.to_target(self);

            // Case 1
            let is_branch_and_key_terminated = self.and(is_branch, key_terminated);
            let case_1_value = self.mul(is_branch_and_key_terminated.target, tree_radix);
            let b = self.not(key_terminated);
            let is_branch_and_key_not_terminated = self.and(is_branch, b);
            let case_2_value = self.mul(is_branch_and_key_not_terminated.target, branch_key_target);
            let case_3_value = self.mul(is_leaf.target, one);

            let c = self.add(case_1_value, case_2_value);
            let updated_current_node_id_idx = self.add(c, case_3_value); // TODO: make this more concise
            let updated_current_node_id =
                decoded_list.select_array(self, updated_current_node_id_idx);
            // If finished == 1, then we should not update the current_node_id
            let current_node_ids =
                Bytes32ArrayTarget::<2>::new([updated_current_node_id, current_node_id].to_vec());
            current_node_id = current_node_ids.select_array(self, finished.target);

            let mut do_path_remainder_check = self.not(finished);
            do_path_remainder_check = self.and(do_path_remainder_check, is_leaf);
            let d = self.or(prefix_extension_even, prefix_extension_odd);
            do_path_remainder_check = self.and(do_path_remainder_check, d);
            let e = self.mul(decoded_element_lens.targets()[0].0, two);
            let f = self.mul(offset, do_path_remainder_check.target);
            let mut check_length = self.sub(e, f);
            check_length = self.mul(check_length, do_path_remainder_check.target);

            // self.assert_subarray_equal(
            //     &path,
            //     offset,
            //     key_path.as_slice(),
            //     current_key_idx,
            //     check_length,
            // );

            current_key_idx = self.add(current_key_idx, is_branch_and_key_not_terminated.target);
            let j = self.mul(is_leaf.target, check_length);
            current_key_idx = self.add(current_key_idx, j);

            let prefix_leaf_even_and_leaf = self.and(prefix_leaf_even, is_leaf);
            let prefix_leaf_odd_and_leaf = self.and(prefix_leaf_odd, is_leaf);
            let l = self.or(is_branch_and_key_terminated, prefix_leaf_even_and_leaf);
            let m = self.or(l, prefix_leaf_odd_and_leaf);
            finished = self.or(finished, m);
        }

        // Can be unsafe because `current_node_id` comes from a ByteVariable.
        let current_node_id_target = current_node_id.as_bytes()[0].to_target(self);
        let borrow = self.zero_u32();
        let (current_node_len, _) =
            self.sub_u32(U32Target(current_node_id_target), const_128, borrow);
        let (lhs_offset, _) = self.sub_u32(const_32, current_node_len, borrow);

        let value_hash = self.mpt_hash(&proof.value_bytes, U32Target::default());
        let value_hash = Bytes32Target::from_biguint_target(self, value_hash.output);

        // self.assert_subarray_equal(
        //     &value.as_bytes(),
        //     lhs_offset,
        //     current_node_id.as_slice(),
        //     one,
        //     current_node_len,
        // );
    }
}

pub trait WitnessMPT<F: PrimeField64>: Witness<F> {
    fn set_u8_slice_input(&mut self, target: &BigUintTarget, input: &[u8]);
    fn set_mpt_proof_target<const DEPTH: usize>(
        &mut self,
        target: &MPTProofTarget<DEPTH>,
        input: MPTInput,
    );
}

impl<T: Witness<F>, F: PrimeField64> WitnessMPT<F> for T {
    fn set_u8_slice_input(&mut self, target: &BigUintTarget, input: &[u8]) {
        let mut input_biguint = BigUint::from_bytes_le(input);

        let input_len_bits = input.len() * 8;
        let num_actual_blocks = 1 + input_len_bits / KECCAK256_R;
        let padded_len_bits = num_actual_blocks * KECCAK256_R;

        // bit right after the end of the message
        input_biguint.set_bit(input_len_bits as u64, true);

        // last bit of the last block
        input_biguint.set_bit(padded_len_bits as u64 - 1, true);

        self.set_biguint_target(target, &input_biguint);
    }

    fn set_mpt_proof_target<const DEPTH: usize>(
        &mut self,
        target: &MPTProofTarget<DEPTH>,
        input: MPTInput,
    ) {
        let proof = input.proof;
        if proof.len() > DEPTH {
            panic!(
                "Proof is too long, has {} elements, but DEPTH is {}",
                proof.len(),
                DEPTH
            );
        }

        // key bytes
        self.set_u8_slice_input(&target.key_bytes, &input.path.as_ref());

        // value bytes
        self.set_u8_slice_input(&target.value_bytes, input.value.as_slice());

        // root
        let root_hash = input.root_hash.as_bytes().to_vec();
        self.set_bytes32_target(&target.root_hash_bytes, root_hash);

        {
            let mut proof_fixed = vec![vec![0u8; ENCODING_LEN]; DEPTH];
            let mut length_nodes_fixed = vec![0u32; DEPTH];

            for (i, inner_vec) in proof.into_iter().enumerate() {
                // Check inner length
                if inner_vec.len() > ENCODING_LEN {
                    panic!(
                        "Proof element {} is too long, has {} elements, but ENCODING_LEN is {}",
                        i,
                        inner_vec.len(),
                        ENCODING_LEN
                    );
                }
                length_nodes_fixed[i] = inner_vec.len() as u32;
                for (j, &byte) in inner_vec.iter().enumerate() {
                    proof_fixed[i][j] = byte;
                }
            }

            // proof
            for (p, t) in proof_fixed.iter().zip(target.proof.iter()) {
                self.set_u8_slice_input(t, p.as_slice());
            }

            // len nodes
            self.set_u32_array_target::<DEPTH>(&target.len_nodes, length_nodes_fixed);
        }
    }
}

pub struct TestInputTarget {
    pub value_bytes: BigUintTarget,
}

pub trait WitnessTest<F: PrimeField64>: Witness<F> {
    fn set_input_target(&mut self, target: &MPTHash, value: &[u8]);
}

impl<T: Witness<F>, F: PrimeField64> WitnessTest<F> for T {
    fn set_input_target(&mut self, target: &MPTHash, value: &[u8]) {
        let mut input_biguint = BigUint::from_bytes_le(value);

        let input_len_bits = value.len() * 8;
        let num_actual_blocks = 1 + input_len_bits / KECCAK256_R;
        let padded_len_bits = num_actual_blocks * KECCAK256_R;

        // bit right after the end of the message
        input_biguint.set_bit(input_len_bits as u64, true);

        // last bit of the last block
        input_biguint.set_bit(padded_len_bits as u64 - 1, true);

        self.set_biguint_target(&target.input, &input_biguint);

        for (i, t) in target.blocks.iter().enumerate() {
            self.set_bool_target(*t, i < num_actual_blocks - 1);
        }
    }
}

// #[test]
// fn test_mpt_hash() {
//     const D: usize = 2;
//     type C = KeccakGoldilocksConfig;
//     type F = <C as GenericConfig<D>>::F;
//     let config = CircuitConfig::standard_recursion_config();
//
//     let mut builder = CircuitBuilder::<F, D>::new(config);
//     let input = builder.add_virtual_test_input_target(136);
//     let hash_output = builder.test_mpt_hash(&input);
//     builder.public_hash_output(&hash_output.output);
//     let num_gates = builder.num_gates();
//     let copy_constraints = "<private>";
//     let data = builder.build::<C>();
//     println!(
//         "keccak256(4) num_gates={}, copy_constraints={}, quotient_degree_factor={}",
//         num_gates, copy_constraints, data.common.quotient_degree_factor
//     );
//
//     let mut pw = PartialWitness::new();
//     {
//         let input_value = hex::decode("02f9010a01840114d8a5b9010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0").unwrap();
//         pw.set_input_target(&hash_output, &input_value);
//     }
//
//     let proof = data.prove(pw).unwrap();
//     println!("public inputs {:?}", proof.public_inputs);
//     public_inputs_to_hex::<F, D>(proof.public_inputs.clone());
//     assert!(data.verify(proof).is_ok());
// }

#[test]
fn test_bit() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();

    let value = vec![129, 144];
    let mut key_bytes_value = BigUint::from_bytes_be(&value);

    let mut pw = PartialWitness::new();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let circuit_key_bytes_value = builder.add_virtual_biguint_target(3);

    let mut key_hexs = Vec::with_capacity(circuit_key_bytes_value.num_limbs());

    for byte in circuit_key_bytes_value.limbs.iter() {
        let bits = builder.low_bits(byte.0, 8, 8);

        let hexs = [4, 0].map(|i| {
            let a: Vec<_> = bits[i..i + 4]
                .iter()
                .map(|x| builder.convert_to_ext(x.target))
                .collect();
            let b: Vec<_> = (0..4)
                .map(|x| {
                    let two_extension = builder.two_extension();
                    builder.exp_u64_extension(two_extension, x)
                })
                .collect();

            let pairs: Vec<_> = a.into_iter().zip(b.into_iter()).collect();

            // sum vec<a>, sum + = a*b
            let zero_extension = builder.zero_extension();
            builder
                .inner_product_extension(F::ONE, zero_extension, pairs)
                .to_target_array()[0]
        });
        key_hexs.push(hexs);
    }

    // set value
    let mut limbs = key_bytes_value.to_bytes_be();
    limbs.resize(circuit_key_bytes_value.num_limbs(), 0);

    for i in 0..circuit_key_bytes_value.num_limbs() {
        pw.set_u32_target(circuit_key_bytes_value.limbs[i], limbs[i] as u32);
    }

    for x in key_hexs {
        for x in x {
            builder.register_public_input(x);
        }
    }

    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();

    println!("public inputs {:?}", proof.public_inputs);
    public_inputs_to_hex::<F, D>(proof.public_inputs.clone());

    data.verify(proof).unwrap();
}
