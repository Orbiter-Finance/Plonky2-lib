use std::marker::PhantomData;

use anyhow::bail;
use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::field::types::PrimeField64;
use plonky2::hash::{hash_types::RichField, poseidon::PoseidonHash};
use plonky2::iop::challenger::{self, RecursiveChallenger};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};
use plonky2_u32::witness::WitnessU32;
use serde::{Deserialize, Serialize};

use crate::eth::utils::CircuitBuilderU32Ext;
use crate::nonnative::biguint::BigUintTarget;
use crate::nonnative::biguint::CircuitBuilderBiguint;
use crate::types::bytes::{
    ByteTarget, Bytes32ArrayTarget, Bytes32Target, BytesTarget, CircuitBuilderBytes,
    U32ArrayTarget, WitnessBytes,
};
use crate::watchers::target_watcher::TargetWatcher;

use super::generator::DecodeRLPNodeGenerator;
use super::utils::{decode_padded_mpt_node, MPTNodeFixedSize};

pub const MAX_MPT_NODE_SIZE: usize = 17;
pub const MAX_RLP_ITEM_SIZE: usize = 32;

#[derive(Clone, Debug)]
pub struct MPTNodeTarget {
    pub data: Bytes32ArrayTarget<MAX_MPT_NODE_SIZE>,
    pub lens: U32ArrayTarget<MAX_MPT_NODE_SIZE>,
    pub len: U32Target,
}

#[derive(Clone, Debug)]
pub struct MPTNodeRLPEncodingTarget<const ENCODING_LEN: usize> {
    pub encoding_bytes_targets: BytesTarget<ENCODING_LEN>,
    pub len: U32Target,
}

#[derive(Clone, Debug)]
pub struct MPTNodeValue<F: RichField> {
    pub data: [[F; MAX_RLP_ITEM_SIZE]; MAX_MPT_NODE_SIZE],
    pub lens: [F; MAX_MPT_NODE_SIZE],
    pub len: F,
}

pub fn get_padded_mpt_node<const ENCODING_LEN: usize>(rlp_encoding: Vec<u8>) -> MPTNodeFixedSize {
    if rlp_encoding.len() > ENCODING_LEN {
        panic!("The length of the RLP encoding is greater than ENCODING_LEN.");
    }

    let mut encoding_fixed_size = [0u8; ENCODING_LEN];
    encoding_fixed_size[..rlp_encoding.len()].copy_from_slice(&rlp_encoding);
    let skip_computation = false;

    let padded_mpt_node =
        decode_padded_mpt_node(&encoding_fixed_size, rlp_encoding.len(), skip_computation);

    padded_mpt_node
}

pub fn convert_to_mpt_node_value<F>(mpt_node_fixed_size: MPTNodeFixedSize) -> MPTNodeValue<F>
where
    F: RichField + Default,
{
    let mut data: [[F; MAX_RLP_ITEM_SIZE]; MAX_MPT_NODE_SIZE] = Default::default();
    let mut lens: [F; MAX_MPT_NODE_SIZE] = Default::default();

    for (i, item) in mpt_node_fixed_size
        .data
        .iter()
        .enumerate()
        .take(mpt_node_fixed_size.len)
    {
        lens[i] = F::from_canonical_usize(item.len);

        for (j, &byte) in item.data.iter().enumerate().take(item.len) {
            data[i][j] = F::from_canonical_u8(byte);
        }
    }

    MPTNodeValue {
        data,
        lens,
        len: F::from_canonical_usize(mpt_node_fixed_size.len),
    }
}

pub trait RLPCircuitBuilder<F: RichField + Extendable<D>, const D: usize> {
    fn add_virtual_decoded_rlp_target(&mut self) -> MPTNodeTarget;
    fn add_virtual_encoded_rlp_target<const ENCODING_LEN: usize>(
        &mut self,
    ) -> MPTNodeRLPEncodingTarget<ENCODING_LEN>;
    fn decode_rlp_to_mpt_node_target<const ENCODING_LEN: usize>(
        &mut self,
        encoded: BytesTarget<ENCODING_LEN>,
        len: U32Target,
        skip_computation: BoolTarget,
    ) -> MPTNodeTarget;

    // The return value (final_claim_poly, challenge) is just for debugging purposes.
    fn verify_decoded_mpt_node<const ENCODING_LEN: usize>(
        &mut self,
        encoded: BytesTarget<ENCODING_LEN>,
        len: U32Target,
        skip_computation: BoolTarget,
        decoded_node: MPTNodeTarget,
    ) -> (Target, Target);

    fn calculate_polynomial_emulating_rlp_encoding(
        &mut self,
        byte_array: &Bytes32Target,
        len: U32Target,
        pow: Target,
    ) -> (Target, Target, U32Target);

    fn add_prefix_polynomial_and_shift(
        &mut self,
        sum_of_rlp_encoding_length: U32Target,
        claim_poly: Target,
        challenge: Target,
    ) -> Target;
}

impl<F: RichField + Extendable<D>, const D: usize> RLPCircuitBuilder<F, D>
    for CircuitBuilder<F, D>
{
    fn add_virtual_encoded_rlp_target<const ENCODING_LEN: usize>(
        &mut self,
    ) -> MPTNodeRLPEncodingTarget<ENCODING_LEN> {
        let bytes = self.add_virtual_bytes_target::<ENCODING_LEN>();
        let len = self.add_virtual_u32_target();
        MPTNodeRLPEncodingTarget {
            encoding_bytes_targets: bytes,
            len,
        }
    }

    fn add_virtual_decoded_rlp_target(&mut self) -> MPTNodeTarget {
        let data = self.add_virtual_bytes32_array_target::<MAX_MPT_NODE_SIZE>();
        let lens = self.add_virtual_u32_array_target::<MAX_MPT_NODE_SIZE>();
        let len = self.add_virtual_u32_target();

        MPTNodeTarget { data, lens, len }
    }

    fn decode_rlp_to_mpt_node_target<const ENCODING_LEN: usize>(
        &mut self,
        encoded: BytesTarget<ENCODING_LEN>,
        len: U32Target,
        skip_computation: BoolTarget,
    ) -> MPTNodeTarget {
        let decoded_rlp_target = self.add_virtual_decoded_rlp_target();
        let encoded_vec = encoded.as_vec();

        let generator = DecodeRLPNodeGenerator::<F, D> {
            encoded: encoded_vec,
            len: len.clone(),
            skip_computation: skip_computation.clone(),
            decoded_mpt_node: decoded_rlp_target.clone(),
            _phantom: PhantomData,
        };

        self.add_simple_generator(generator);

        let (final_claim_poly, challenge) = self.verify_decoded_mpt_node::<ENCODING_LEN>(
            encoded.clone(),
            len.clone(),
            skip_computation.clone(),
            decoded_rlp_target.clone(),
        );

        decoded_rlp_target
    }

    fn verify_decoded_mpt_node<const ENCODING_LEN: usize>(
        &mut self,
        encoded: BytesTarget<ENCODING_LEN>,
        len: U32Target,
        skip_computation: BoolTarget,
        decoded_node: MPTNodeTarget,
    ) -> (Target, Target) {
        let mut challenger = RecursiveChallenger::<F, PoseidonHash, D>::new(self);

        // Give the challenger the encoded string.
        let encoded_bit_targets: Vec<Target> = encoded
            .as_vec()
            .iter()
            .flat_map(|byte_target| byte_target.as_le_bits())
            .map(|bit_target| bit_target.target)
            .collect();
        let encoded_bytes_len = len.0;
        challenger.observe_elements(&encoded_bit_targets);
        challenger.observe_element(encoded_bytes_len);

        // Give the challenger the output of the hint which decodes `encoded`. In other words, this
        // is what we're trying to verify. It is ABSOLUTELY essential that we pass in `mpt` here to
        // generate challengers as otherwise one can manipulate the polynomial to get 0.

        let decoded_bytes_vec_target: Vec<Target> = decoded_node
            .data
            .as_slice()
            .iter()
            .flat_map(|bytes32| bytes32.as_bytes().to_vec())
            .flat_map(|byte| byte.as_le_bits())
            .map(|bit_target| bit_target.target)
            .collect();
        let decoded_bytes_lens_target: Vec<Target> = decoded_node
            .lens
            .targets()
            .iter()
            .map(|u32target| u32target.0)
            .collect();
        let decoded_len_target = decoded_node.len.0;

        challenger.observe_elements(&decoded_bytes_vec_target);
        challenger.observe_elements(&decoded_bytes_lens_target);
        challenger.observe_element(decoded_len_target);

        challenger.observe_element(skip_computation.target);

        let challenge = challenger.get_challenge(self);

        self.watch(&challenge.clone(), &"challenge");

        let one = self.one();
        let zero = self.zero();
        let true_bool = self.constant_bool(true);
        let mut encoding_poly = self.zero();
        let mut pow = self.one();

        let encoded_vec = encoded.as_vec();
        for i in 0..ENCODING_LEN {
            let mut current_term = encoded_vec[i].to_target(self);

            // TODO: should we use cubic extension?
            current_term = self.mul(current_term, pow);
            // It's okay to simply add current_term as pow becomes 0 once i = ENCODING_LEN.
            encoding_poly = self.add(encoding_poly, current_term);

            let index = self.constant_u32(i as u32);
            let index_le_len = self.is_less_than_u32(index, len, 32);
            let pow_multiplier = self.select(index_le_len, challenge, zero);

            pow = self.mul(pow, pow_multiplier);
        }

        let mut sum_of_rlp_encoding_length = self.zero_u32();
        let mut claim_poly = zero;
        pow = one;

        for i in 0..MAX_MPT_NODE_SIZE {
            let index_i = self.constant_u32(i as u32);
            let index_le_len = self.is_less_than_u32(index_i, decoded_node.len, 32);

            let (mut poly, mut next_pow, mut encoding_len) = self
                .calculate_polynomial_emulating_rlp_encoding(
                    &decoded_node.data.0[i],
                    decoded_node.lens.0[i],
                    challenge,
                );

            // Shift the `poly` value by the appropriate power of `challenger`, and also check
            // if we should even include this.
            poly = self.select(index_le_len, poly, zero);
            poly = self.mul(poly, pow);
            claim_poly = self.add(claim_poly, poly);

            next_pow = self.select(index_le_len, next_pow, one);
            pow = self.mul(pow, next_pow);

            encoding_len = self.select_u32(index_le_len, encoding_len, U32Target(zero));
            (sum_of_rlp_encoding_length, _) =
                self.add_u32(sum_of_rlp_encoding_length, encoding_len);
        }

        let final_claim_poly =
            self.add_prefix_polynomial_and_shift(sum_of_rlp_encoding_length, claim_poly, challenge);
        self.watch(&final_claim_poly, "claim_poly");
        self.watch(&encoding_poly, "encoding_poly");

        let claim_poly_equals_encoding_poly = self.is_equal(final_claim_poly, encoding_poly);
        let result = self.or(skip_computation, claim_poly_equals_encoding_poly);

        self.connect(result.target, true_bool.target);

        (final_claim_poly, challenge)
    }

    /// Evaluate the polynomial constructed from seeing RLP-encode(byte_array) as a vector of
    /// coefficients and x = pow.
    ///
    /// Mathematically speaking, we define a function `f(E : RLP-encoding) -> F` such that
    /// `f(E) = \sigma_{i = 0}^{len(E) - 1} [byte_to_field_element(coefficients[i]) * pow^(i)]`.
    ///
    /// This function returns:
    /// 1. `f(RLP-encoding(E))`,
    /// 2. `pow^len(RLP-encoding(E))`, which can be seen as the "next" power,
    /// 3. `len(RLP-encoding(coefficients))`, which is necessary for calculating the prefix byte for
    ///    `RLP-encoding(mpt)`.
    ///
    /// Note that, as specified in the function name, we don't actually calculate
    /// `RLP-encoding(byte_array)`.
    fn calculate_polynomial_emulating_rlp_encoding(
        &mut self,
        byte_array: &Bytes32Target,
        len: U32Target,
        pow: Target,
    ) -> (Target, Target, U32Target) {
        let true_bool = self.constant_bool(true);
        let zero = self.zero();
        let one = self.one();
        let cons55 = self.constant_u32(56);

        // TODO: It's likely that we'll need to implement the case when the given byte string is
        // >= 56 bytes. (e.g., account state) However, for the first iteration, we will only worry
        // about the case when the byte string is <= 55 bytes.
        let len_lte_55 = self.is_less_than_u32(len, cons55, 32);

        self.connect(len_lte_55.target, true_bool.target);

        // There are 2 possible outcomes of encode(byte_array):
        //
        // 1. len = 1 && byte_array[0] <  0x80  =>  {byte_array[0]}
        // 2. else                              =>  {0x80 + len, byte_array[0], byte_array[1], ...}

        let cons0x80 = self.constant_u32(128);

        let first_byte_as_target = byte_array.0[0].to_target(self);
        let len1 = one;
        let res_case_1 = first_byte_as_target;

        let mut res_case_2 = self.add(len.0, cons0x80.0);
        let len2 = self.add(len.0, one);
        let mut next_pow = pow;

        for i in 0..32 {
            let index = self.constant_u32(i as u32);
            let index_le_len = self.is_less_than_u32(index, len, 32);

            let mut current_term = byte_array.0[i].to_target(self);
            current_term = self.mul(current_term, next_pow);
            current_term = self.select(index_le_len, current_term, zero);
            res_case_2 = self.add(res_case_2, current_term);

            let pow_multiplier = self.select(index_le_len, pow, one);
            next_pow = self.mul(next_pow, pow_multiplier);
        }

        let is_len_1 = self.is_equal(len.0, one);
        let is_first_variable_less_than_0x80 =
            self.is_less_than_u32(U32Target(first_byte_as_target), cons0x80, 32);
        let is_case_1 = self.and(is_len_1, is_first_variable_less_than_0x80);

        let res_len = self.select(is_case_1, len1, len2);
        let res_pow = self.select(is_case_1, pow, next_pow);
        let res = self.select(is_case_1, res_case_1, res_case_2);

        let res_len_u32 = self.from_target_to_u32_safe(res_len);

        (res, res_pow, res_len_u32)
    }

    /// Add in the term corresponding to the prefix byte(s) of the RLP-encoding, given the sum of
    /// the item-wise polynomial.
    ///
    /// The RLP-encoding is in the form of `{ prefix, prefix_0, byte_array_0, prefix_1,
    /// byte_array_1, ... }`. And so far, we have calculated the polynomial for {prefix_0,
    /// byte_array_0, prefix_1, byte_array_1, ...}. Now we have to calculate `prefix`, and
    /// also "shift" the current polynomial. This logic isn't necessarily reusable or modular, but
    /// it's complex logic that blurs out the whole `verify_decoded_mpt_node` function, so this is
    /// a separate function.
    fn add_prefix_polynomial_and_shift(
        &mut self,
        sum_of_rlp_encoding_length: U32Target,
        claim_poly: Target,
        challenge: Target,
    ) -> Target {
        let cons56 = self.constant_u32(56);
        let cons256 = self.constant_u32(256);
        let cons65536 = self.constant_u32(65536);
        let cons0xf8 = self.constant_u32(248);

        // Assert that sum_of_rlp_encoding_length is less than 256^2 = 65536 bits. A
        // well-formed MPT should never need that many bytes.
        self.check_less_than_u32(sum_of_rlp_encoding_length, cons65536, 32);

        // The main idea is to convert claim_poly into `prefix_term + [appropriate power of
        // challenger] * claim_poly`. There are three cases that we work on:
        // 1.        combined length <  56    => prefix = {0xc0 + combined length}
        // 2.  56 <= combined length <  256   => prefix = {0xf8, combined length in 1 byte}
        // 3. 256 <= combined length < 65536  => prefix = {0xf9, combined length in 2 bytes}
        //
        // RLP technically allows a longer byte string, but we will not implement it, at least, for
        // now.

        // Case 1: We need 0xc0 + combined_length + claim_poly * challenge.
        let mut case_1 = self.constant(F::from_canonical_u32(192));
        case_1 = self.add(case_1, sum_of_rlp_encoding_length.0);
        let case_1_poly = self.mul(claim_poly, challenge);
        case_1 = self.add(case_1, case_1_poly);

        // Case 2: We need 0xf8 + combined_length * challenger + claim_poly * (challenge ^ 2).
        let mut case_2 = self.mul(sum_of_rlp_encoding_length.0, challenge);
        case_2 = self.add(case_2, cons0xf8.0);
        let mut case_2_poly = self.mul(claim_poly, challenge);
        case_2_poly = self.mul(case_2_poly, challenge);
        case_2 = self.add(case_2, case_2_poly);

        // Case 3
        //
        // Divide sum_of_rlp_encoding_length by cons256 and get the quotient and remainder, and we
        // need 0xf9 + div * challenger + rem * (challenger ^ 2) + claim_poly * (challenger ^ 3).

        let lhs = BigUintTarget {
            limbs: vec![sum_of_rlp_encoding_length],
        };
        let rhs = BigUintTarget {
            limbs: vec![cons256],
        };
        let (div_in_biguint, rem_in_biguint) = self.div_rem_biguint(&lhs, &rhs);

        // only take the least significant u32 limb
        let mut div = div_in_biguint.limbs[0].0;
        let mut rem = rem_in_biguint.limbs[0].0;

        let mut case_3 = self.constant(F::from_canonical_u32(249));

        div = self.mul(div, challenge);
        case_3 = self.add(case_3, div);

        rem = self.mul(rem, challenge);
        rem = self.mul(rem, challenge);
        case_3 = self.add(case_3, rem);

        let mut case_3_poly = self.mul(claim_poly, challenge);
        case_3_poly = self.mul(case_3_poly, challenge);
        case_3_poly = self.mul(case_3_poly, challenge);

        case_3 = self.add(case_3, case_3_poly);

        // Pick the right solution
        // TODO: since sum_of_rlp_encoding_length < 65536, we can set num_bits to 16 in the below comparison
        let encoding_len_le_256 = self.is_less_than_u32(sum_of_rlp_encoding_length, cons256, 32);
        let mut res = self.select(encoding_len_le_256, case_2, case_3);
        let encoding_len_le_56 = self.is_less_than_u32(sum_of_rlp_encoding_length, cons56, 32);
        res = self.select(encoding_len_le_56, case_1, res);
        res
    }
}

pub fn fill_encoded_rlp_target<F: RichField, const ENCODING_LEN: usize>(
    witness: &mut impl WitnessBytes<F>,
    encoded_bytes: &[u8; ENCODING_LEN],
    len: u32,
    encoded_rlp_target: MPTNodeRLPEncodingTarget<ENCODING_LEN>,
) {
    let encoded_bytes_vec: Vec<u8> = encoded_bytes.iter().map(|&byte| byte as u8).collect();
    witness.set_bytes_target(
        &encoded_rlp_target.encoding_bytes_targets,
        encoded_bytes_vec,
    );
    witness.set_u32_target(encoded_rlp_target.len, len)
}

pub fn fill_decoded_rlp_target<F: RichField>(
    witness: &mut (impl WitnessBytes<F> + WitnessU32<F>),
    mpt_node_target: &MPTNodeTarget,
    mpt_node_fixed_size: &MPTNodeFixedSize,
) {
    // Convert and set the `data` field
    // for (index, item) in mpt_node_fixed_size.data.iter().enumerate() {
    //     let data_as_u32: Vec<u32> = item.data.iter().map(|&byte| byte as u32).collect();
    //     witness.set_bytes32_target(&mpt_node_target.data.0[index], data_as_u32);
    // }

    let data_for_target: Vec<Vec<u8>> = mpt_node_fixed_size
        .data
        .iter()
        .map(|item| item.data.iter().map(|&byte| byte as u8).collect())
        .collect();

    witness.set_bytes32_array_target::<MAX_MPT_NODE_SIZE>(&mpt_node_target.data, data_for_target);

    // Set the `lens` field
    let lens_as_u32: Vec<u32> = mpt_node_fixed_size
        .data
        .iter()
        .map(|item| item.len as u32)
        .collect();
    witness.set_u32_array_target::<MAX_MPT_NODE_SIZE>(&mpt_node_target.lens, lens_as_u32);

    // Set the `len` field
    witness.set_u32_target(mpt_node_target.len, mpt_node_fixed_size.len as u32);
}

#[cfg(test)]
mod tests {

    use crate::{
        bytes, profiling_enable,
        watchers::{bytes_watcher::BytesWatcher, target_watcher::TargetWatcher},
    };

    use super::*;
    use anyhow::{Ok, Result};
    use plonky2::{
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };

    // rlp test with watchers
    fn test_verify_decoded_mpt_node<const ENCODING_LEN: usize, F>(
        rlp_encoding: Vec<u8>,
        fuzzer: F,
    ) -> Result<()>
    where
        F: Fn([u8; ENCODING_LEN]) -> [u8; ENCODING_LEN],
    {
        // profiling_enable();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();

        let mut builder = CircuitBuilder::<F, D>::new(config);

        let encoded_rlp_target = builder.add_virtual_encoded_rlp_target::<ENCODING_LEN>();
        let skip_computation_target = builder.add_virtual_bool_target_safe();
        let encoded_bytes_target = encoded_rlp_target.clone().encoding_bytes_targets;
        let encoded_bytes_len = encoded_rlp_target.clone().len;
        let decoded_mpt_node_target = builder.decode_rlp_to_mpt_node_target(
            encoded_bytes_target.clone(),
            encoded_bytes_len.clone(),
            skip_computation_target.clone(),
        );

        // the builder.decode_rlp_to_mpt_node_target above already has verify_decoded_mpt_node, here we just debug it
        let (final_claim_poly, challenge) = builder.verify_decoded_mpt_node::<ENCODING_LEN>(
            encoded_bytes_target.clone(),
            encoded_bytes_len.clone(),
            skip_computation_target.clone(),
            decoded_mpt_node_target.clone(),
        );

        // use fuzz_target for testing purposes
        let encoded_fuzz_target = builder.add_virtual_encoded_rlp_target::<ENCODING_LEN>();
        let encoded_fuzz_vec = encoded_fuzz_target.clone().encoding_bytes_targets.as_vec();
        let fuzz_len = encoded_fuzz_target.clone().len;
        builder.watch(&fuzz_len.0, "fuzz_len");

        let mut encoding_poly_fuzz = builder.zero();
        let mut pow = builder.one();

        let zero = builder.zero();

        for i in 0..ENCODING_LEN {
            let mut current_term = encoded_fuzz_vec[i].to_target(&mut builder);

            current_term = builder.mul(current_term, pow);
            // It's okay to simply add current_term as pow becomes 0 once i = ENCODING_LEN.
            encoding_poly_fuzz = builder.add(encoding_poly_fuzz, current_term);

            let index = builder.constant_u32(i as u32);
            let index_le_len = builder.is_less_than_u32(index, fuzz_len, 32);
            let pow_multiplier = builder.select(index_le_len, challenge, zero);
            pow = builder.mul(pow, pow_multiplier);
            // builder.watch(&pow, &"!current_pow");
            // builder.watch(&high_bits.0, &"!high_bits");
        }

        builder.connect(encoding_poly_fuzz, final_claim_poly);
        builder.watch(&encoding_poly_fuzz, "fuzz encoding poly");
        // Splitting decoded_rlp_target for watcher debugging purposes
        // let decoded_bytes_vec: Vec<Vec<ByteTarget>> = decoded_mpt_node_target
        //     .data
        //     .as_slice()
        //     .iter()
        //     .map(|bytes32| bytes32.as_bytes().to_vec())
        //     .collect();
        // let decoded_bytes_lens = decoded_mpt_node_target.lens;
        // let decoded_len = decoded_mpt_node_target.len;

        // decoded_bytes_vec
        //     .into_iter()
        //     .for_each(|bytes32| builder.watch_bytes(bytes32.as_slice(), &"decoded bytes32: "));
        // decoded_bytes_lens
        //     .0
        //     .into_iter()
        //     .for_each(|len| builder.watch(&len.0, &"each decoded bytes32 valid len: "));
        // builder.watch(&decoded_len.0, "valid decoded bytes32 num:");

        let data = builder.build::<C>();

        // prepare input data
        let mut encoding_fixed_size = [0u8; ENCODING_LEN];
        encoding_fixed_size[..rlp_encoding.len()].copy_from_slice(&rlp_encoding);
        let len = rlp_encoding.len();
        let skip_computation = false;

        // fill input data in the circuit
        let encoding_fixed_size_fuzz = fuzzer(encoding_fixed_size);
        for _ in 0..1 {
            let mut pw = PartialWitness::new();
            fill_encoded_rlp_target(
                &mut pw,
                &encoding_fixed_size,
                len as u32,
                encoded_rlp_target.clone(),
            );
            fill_encoded_rlp_target(
                &mut pw,
                &encoding_fixed_size_fuzz,
                len as u32,
                encoded_fuzz_target.clone(),
            );
            println!("!!!len: {}", len);
            pw.set_bool_target(skip_computation_target.clone(), skip_computation);

            let proof = data.prove(pw).unwrap();
            println!("proof PIS {:?}", proof.public_inputs);
            let result = data.verify(proof);
            println!("Verify result: {:?}", result);
            assert!(result.is_ok());
            println!("prove and verify proof success!!!");
        }
        Ok(())
    }

    #[test]
    fn test_verify_decoded_mpt_node_extension_node() {
        const ENCODING_LEN: usize = 2 * 32 + 20;

        // This is an RLP-encoded list of an extension node. The 00 in 0x006f indicates that the path
        // length is even, and the path is 6 -> f. This extension node points to a leaf node with
        // the hash starting with 0x188d11.  ["0x006f",
        // "0x188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6"]
        let rlp_encoding: Vec<u8> =
            bytes!("0xe482006fa0188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6");

        test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, |x| x);
    }

    #[test]
    fn test_verify_decoded_mpt_node_extension_node_mid_length() {
        const ENCODING_LEN: usize = 120;

        // This is an RLP-encoded list of an extension node. Both the first and second elements are
        // 32 bytes. The whole encoding is 68 bytes, and this is suitable for testing a list whose
        // length can be represented in 1 byte.
        let rlp_encoding: Vec<u8> =
            bytes!("0xf842a01111111111111111111111111111111111111111111111111111111111111111a01111111111111111111111111111111111111111111111111111111111111111");

        test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, |x| x);
    }

    #[test]
    fn test_verify_decoded_mpt_node_branch_node() {
        const ENCODING_LEN: usize = 600;

        // This is a RLP-encoded list of a branch node. It is a list of length 17. Each of the first
        // 16 elements is a 32-byte hash, and the last element is 0.
        let rlp_encoding: Vec<u8>  = bytes!("0xf90211a0215ead887d4da139eba306f76d765f5c4bfb03f6118ac1eb05eec3a92e1b0076a03eb28e7b61c689fae945b279f873cfdddf4e66db0be0efead563ea08bc4a269fa03025e2cce6f9c1ff09c8da516d938199c809a7f94dcd61211974aebdb85a4e56a0188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6a0b281bb20061318a515afbdd02954740f069ebc75e700fde24dfbdf8c76d57119a0d8d77d917f5b7577e7e644bbc7a933632271a8daadd06a8e7e322f12dd828217a00f301190681b368db4308d1d1aa1794f85df08d4f4f646ecc4967c58fd9bd77ba0206598a4356dd50c70cfb1f0285bdb1402b7d65b61c851c095a7535bec230d5aa000959956c2148c82c207272af1ae129403d42e8173aedf44a190e85ee5fef8c3a0c88307e92c80a76e057e82755d9d67934ae040a6ec402bc156ad58dbcd2bcbc4a0e40a8e323d0b0b19d37ab6a3d110de577307c6f8efed15097dfb5551955fc770a02da2c6b12eedab6030b55d4f7df2fb52dab0ef4db292cb9b9789fa170256a11fa0d00e11cde7531fb79a315b4d81ea656b3b452fe3fe7e50af48a1ac7bf4aa6343a066625c0eb2f6609471f20857b97598ae4dfc197666ff72fe47b94e4124900683a0ace3aa5d35ba3ebbdc0abde8add5896876b25261717c0a415c92642c7889ec66a03a4931a67ae8ebc1eca9ffa711c16599b86d5286504182618d9c2da7b83f5ef780");
        test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, |x| x);
    }

    #[test]
    fn test_verify_decoded_mpt_node_leaf_node_single_bytes() {
        const ENCODING_LEN: usize = 40;

        // This is a RLP-encoded list of a leaf node, ["0x30", "0xff"]
        let rlp_encoding: Vec<u8> = bytes!("0xc33081ff");
        test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, |x| x);
    }

    // #[test]
    // #[should_panic]
    // fn test_verify_decode_long_rlp_encoding() {
    //     const ENCODING_LEN: usize = 1200;
    //     let rlp_encoding: Vec<u8> = bytes!("b904004c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e73656374657475722061646970697363696e6720656c69742e20437572616269747572206d6175726973206d61676e612c20737573636970697420736564207665686963756c61206e6f6e2c20696163756c697320666175636962757320746f72746f722e2050726f696e20737573636970697420756c74726963696573206d616c6573756164612e204475697320746f72746f7220656c69742c2064696374756d2071756973207472697374697175652065752c20756c7472696365732061742072697375732e204d6f72626920612065737420696d70657264696574206d6920756c6c616d636f7270657220616c6971756574207375736369706974206e6563206c6f72656d2e2041656e65616e2071756973206c656f206d6f6c6c69732c2076756c70757461746520656c6974207661726975732c20636f6e73657175617420656e696d2e204e756c6c6120756c74726963657320747572706973206a7573746f2c20657420706f73756572652075726e6120636f6e7365637465747572206e65632e2050726f696e206e6f6e20636f6e76616c6c6973206d657475732e20446f6e65632074656d706f7220697073756d20696e206d617572697320636f6e67756520736f6c6c696369747564696e2e20566573746962756c756d20616e746520697073756d207072696d697320696e206661756369627573206f726369206c756374757320657420756c74726963657320706f737565726520637562696c69612043757261653b2053757370656e646973736520636f6e76616c6c69732073656d2076656c206d617373612066617563696275732c2065676574206c6163696e6961206c616375732074656d706f722e204e756c6c61207175697320756c747269636965732070757275732e2050726f696e20617563746f722072686f6e637573206e69626820636f6e64696d656e74756d206d6f6c6c69732e20416c697175616d20636f6e73657175617420656e696d206174206d65747573206c75637475732c206120656c656966656e6420707572757320656765737461732e20437572616269747572206174206e696268206d657475732e204e616d20626962656e64756d2c206e6571756520617420617563746f72207472697374697175652c206c6f72656d206c696265726f20616c697175657420617263752c206e6f6e20696e74657264756d2074656c6c7573206c65637475732073697420616d65742065726f732e20437261732072686f6e6375732c206d65747573206163206f726e617265206375727375732c20646f6c6f72206a7573746f20756c747269636573206d657475732c20617420756c6c616d636f7270657220766f6c7574706174");
    //     test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, |x| x);
    // }

    #[test]
    #[should_panic]
    fn test_verify_decoded_mpt_node_branch_node_fuzzed_prefix() {
        const ENCODING_LEN: usize = 600;

        // This is a RLP-encoded list of a branch node. It is a list of length 17. Each of the first
        // 16 elements is a 32-byte hash, and the last element is 0.
        let rlp_encoding: Vec<u8>  = bytes!("0xf90211a0215ead887d4da139eba306f76d765f5c4bfb03f6118ac1eb05eec3a92e1b0076a03eb28e7b61c689fae945b279f873cfdddf4e66db0be0efead563ea08bc4a269fa03025e2cce6f9c1ff09c8da516d938199c809a7f94dcd61211974aebdb85a4e56a0188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6a0b281bb20061318a515afbdd02954740f069ebc75e700fde24dfbdf8c76d57119a0d8d77d917f5b7577e7e644bbc7a933632271a8daadd06a8e7e322f12dd828217a00f301190681b368db4308d1d1aa1794f85df08d4f4f646ecc4967c58fd9bd77ba0206598a4356dd50c70cfb1f0285bdb1402b7d65b61c851c095a7535bec230d5aa000959956c2148c82c207272af1ae129403d42e8173aedf44a190e85ee5fef8c3a0c88307e92c80a76e057e82755d9d67934ae040a6ec402bc156ad58dbcd2bcbc4a0e40a8e323d0b0b19d37ab6a3d110de577307c6f8efed15097dfb5551955fc770a02da2c6b12eedab6030b55d4f7df2fb52dab0ef4db292cb9b9789fa170256a11fa0d00e11cde7531fb79a315b4d81ea656b3b452fe3fe7e50af48a1ac7bf4aa6343a066625c0eb2f6609471f20857b97598ae4dfc197666ff72fe47b94e4124900683a0ace3aa5d35ba3ebbdc0abde8add5896876b25261717c0a415c92642c7889ec66a03a4931a67ae8ebc1eca9ffa711c16599b86d5286504182618d9c2da7b83f5ef780");
        let fuzz = |x: [u8; ENCODING_LEN]| {
            let mut y = x;
            y[0] = 0xe;
            y
        };
        test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, fuzz);
    }

    #[test]
    #[should_panic]
    fn test_verify_decoded_mpt_node_branch_node_fuzzed_body() {
        const ENCODING_LEN: usize = 600;

        // This is a RLP-encoded list of a branch node. It is a list of length 17. Each of the first
        // 16 elements is a 32-byte hash, and the last element is 0.
        let rlp_encoding: Vec<u8>  = bytes!("0xf90211a0215ead887d4da139eba306f76d765f5c4bfb03f6118ac1eb05eec3a92e1b0076a03eb28e7b61c689fae945b279f873cfdddf4e66db0be0efead563ea08bc4a269fa03025e2cce6f9c1ff09c8da516d938199c809a7f94dcd61211974aebdb85a4e56a0188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6a0b281bb20061318a515afbdd02954740f069ebc75e700fde24dfbdf8c76d57119a0d8d77d917f5b7577e7e644bbc7a933632271a8daadd06a8e7e322f12dd828217a00f301190681b368db4308d1d1aa1794f85df08d4f4f646ecc4967c58fd9bd77ba0206598a4356dd50c70cfb1f0285bdb1402b7d65b61c851c095a7535bec230d5aa000959956c2148c82c207272af1ae129403d42e8173aedf44a190e85ee5fef8c3a0c88307e92c80a76e057e82755d9d67934ae040a6ec402bc156ad58dbcd2bcbc4a0e40a8e323d0b0b19d37ab6a3d110de577307c6f8efed15097dfb5551955fc770a02da2c6b12eedab6030b55d4f7df2fb52dab0ef4db292cb9b9789fa170256a11fa0d00e11cde7531fb79a315b4d81ea656b3b452fe3fe7e50af48a1ac7bf4aa6343a066625c0eb2f6609471f20857b97598ae4dfc197666ff72fe47b94e4124900683a0ace3aa5d35ba3ebbdc0abde8add5896876b25261717c0a415c92642c7889ec66a03a4931a67ae8ebc1eca9ffa711c16599b86d5286504182618d9c2da7b83f5ef780");
        let fuzz = |x: [u8; ENCODING_LEN]| {
            let mut y = x;
            y[100] += 1;
            y
        };
        test_verify_decoded_mpt_node::<ENCODING_LEN, _>(rlp_encoding, fuzz);
    }

    // Please close the global profile enabling before this batch test
    #[test]
    fn test_verify_decoded_mpt_node_branch_node_batch_fuzzed_body() {
        const ENCODING_LEN: usize = 600;
        let mut unexpected_pass_indices = Vec::new();
        // RLP-encoded list as before...
        let rlp_encoding: Vec<u8> = bytes!("0xf90211a0215ead887d4da139eba306f76d765f5c4bfb03f6118ac1eb05eec3a92e1b0076a03eb28e7b61c689fae945b279f873cfdddf4e66db0be0efead563ea08bc4a269fa03025e2cce6f9c1ff09c8da516d938199c809a7f94dcd61211974aebdb85a4e56a0188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6a0b281bb20061318a515afbdd02954740f069ebc75e700fde24dfbdf8c76d57119a0d8d77d917f5b7577e7e644bbc7a933632271a8daadd06a8e7e322f12dd828217a00f301190681b368db4308d1d1aa1794f85df08d4f4f646ecc4967c58fd9bd77ba0206598a4356dd50c70cfb1f0285bdb1402b7d65b61c851c095a7535bec230d5aa000959956c2148c82c207272af1ae129403d42e8173aedf44a190e85ee5fef8c3a0c88307e92c80a76e057e82755d9d67934ae040a6ec402bc156ad58dbcd2bcbc4a0e40a8e323d0b0b19d37ab6a3d110de577307c6f8efed15097dfb5551955fc770a02da2c6b12eedab6030b55d4f7df2fb52dab0ef4db292cb9b9789fa170256a11fa0d00e11cde7531fb79a315b4d81ea656b3b452fe3fe7e50af48a1ac7bf4aa6343a066625c0eb2f6609471f20857b97598ae4dfc197666ff72fe47b94e4124900683a0ace3aa5d35ba3ebbdc0abde8add5896876b25261717c0a415c92642c7889ec66a03a4931a67ae8ebc1eca9ffa711c16599b86d5286504182618d9c2da7b83f5ef780");

        for i in 0..rlp_encoding.len() {
            let mut current_rlp = rlp_encoding.clone();

            let fuzzer = move |rlp: [u8; ENCODING_LEN]| -> [u8; ENCODING_LEN] {
                let mut y = rlp;
                if i < y.len() {
                    y[i] = y[i].wrapping_add(1);
                }
                y
            };

            // Note: You need to handle the panic for each test to ensure all bytes are tested.
            // This could be done with std::panic::catch_unwind or similar.
            let result = std::panic::catch_unwind(|| {
                test_verify_decoded_mpt_node::<ENCODING_LEN, _>(current_rlp, fuzzer);
            });

            if result.is_ok() {
                unexpected_pass_indices.push(i);
            }
        }

        if !unexpected_pass_indices.is_empty() {
            let passed_msg = unexpected_pass_indices
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(", ");

            panic!("Test unexpectedly passed at indices: {}", passed_msg);
        }
    }
}
