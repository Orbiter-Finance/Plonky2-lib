use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::hash::{hash_types::RichField, poseidon::PoseidonHash};
use plonky2::iop::challenger::RecursiveChallenger;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};
use serde::{Deserialize, Serialize};

use crate::types::bytes::{ArrayTarget, ByteTarget, Bytes32ArrayTarget, Bytes32Target};

use super::utils::{decode_padded_mpt_node, MPTNodeFixedSize};
// use plonky2x::frontend::extension::CubicExtensionVariable;
// use plonky2x::frontend::hint::simple::hint::Hint;
// use plonky2x::prelude::{
//     ArrayVariable, BoolVariable, ByteVariable, CircuitBuilder, CircuitVariable, PlonkParameters,
//     RichField, U32Variable, ValueStream, Variable, VariableStream,
// };

pub const MAX_MPT_NODE_SIZE: usize = 17;
pub const MAX_RLP_ITEM_SIZE: usize = 32;

// #[derive(Clone, Debug, CircuitVariable)]
// #[value_name(MPTValueType)]
#[derive(Clone, Debug)]
pub struct MPTNodeTarget {
    pub data: Bytes32ArrayTarget<MAX_MPT_NODE_SIZE>,
    pub lens: ArrayTarget<MAX_MPT_NODE_SIZE>,
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

// impl MPTNodeFixedSize {
//     /// Convert `MPTNodeFixedSize` into `MPTValueType<F>`
//     fn to_value_type<F: RichField>(self) -> MPTNodeValue<F> {
//         MPTNodeValue::<F> {
//             data: self.data.iter().map(|x| x.data.to_vec()).collect_vec(),
//             lens: self
//                 .data
//                 .iter()
//                 .map(|x| F::from_canonical_usize(x.len))
//                 .collect_vec(),
//             len: F::from_canonical_usize(self.len),
//         }
//     }
// }

/// A Hint structure to decode an RLP-encoded string.
///
/// The RLP-encoded string is expected to be padded to a fixed size. The fixed size should equal
/// `ENCODING_LEN` and is specified as a type parameter. The "true" length of the encoding is given
/// in the stream. `LIST_LEN` specifies the node size. (e.g., 2 for extension/leaf nodes, 17 for
/// branch nodes.) The decoded string is returned as a padded 2-dimensional byte array
/// (`MAX_RLP_ITEM_SIZE` x `LIST_LEN`).
// #[derive(Debug, Clone, Serialize, Deserialize)]
// struct DecodeHint<const ENCODING_LEN: usize> {}
// impl<L: PlonkParameters<D>, const D: usize, const ENCODING_LEN: usize> Hint<L, D>
//     for DecodeHint<ENCODING_LEN>
// {
//     fn hint(&self, input_stream: &mut ValueStream<L, D>, output_stream: &mut ValueStream<L, D>) {
//         let encoded = input_stream.read_value::<ArrayVariable<ByteVariable, ENCODING_LEN>>();
//         let len = input_stream.read_value::<Variable>();
//         let skip_computation = input_stream.read_value::<BoolVariable>();

//         let decoded =
//             decode_padded_mpt_node(&encoded, len.as_canonical_u64() as usize, skip_computation);

//         output_stream.write_value::<MPTVariable>(decoded.to_value_type());
//     }
// }

pub trait RLPCircuitBuilder<F: RichField + Extendable<D>, const D: usize> {
    fn add_virtual_decoded_rlp_target(&mut self) -> MPTNodeTarget;
    fn add_virtual_encoded_rlp_target<const ENCODING_LEN: usize>(
        &mut self,
    ) -> Bytes32ArrayTarget<ENCODING_LEN>;
    // fn if_less_than_else<T: CircuitVariable>(
    //     &mut self,
    //     a: U32Variable,
    //     b: U32Variable,
    //     c: T,
    //     d: T,
    // ) -> T;

    // fn calculate_polynomial_emulating_rlp_encoding_cubic(
    //     &mut self,
    //     byte_array: Bytes32Target,
    //     len: U32Target,
    //     pow: U32Target,
    // ) -> (U32Target, U32Target, U32Target);
    // fn add_prefix_polynomial_and_shift(
    //     &mut self,
    //     sum_of_rlp_encoding_length: U32Variable,
    //     claim_poly: CubicExtensionVariable,
    //     challenge: CubicExtensionVariable,
    // ) -> CubicExtensionVariable;
    // fn verify_decoded_mpt_node<const ENCODING_LEN: usize>(
    //     &mut self,
    //     encoded: &ArrayVariable<ByteVariable, ENCODING_LEN>,
    //     len: U32Variable,
    //     skip_computation: BoolVariable,
    //     mpt: &MPTVariable,
    // );

    // fn decode_mpt_node<const ENCODING_LEN: usize, const ELEMENT_LEN: usize>(
    //     &mut self,
    //     encoded: ArrayVariable<ByteVariable, ENCODING_LEN>,
    //     len: Variable,
    //     skip_computation: BoolVariable,
    // ) -> MPTVariable;
}

impl<F: RichField + Extendable<D>, const D: usize> RLPCircuitBuilder<F, D>
    for CircuitBuilder<F, D>
{
    // / Helper function. Equivalent to `(a < b) ? c : d`.
    // fn if_less_than_else<T: CircuitVariable>(
    //     &mut self,
    //     a: U32Variable,
    //     b: U32Variable,
    //     c: T,
    //     d: T,
    // ) -> T {
    //     let a_lt_b = self.lt(a, b);
    //     self.select::<T>(a_lt_b, c, d)
    // }

    // / Evaluate the polynomial constructed from seeing RLP-encode(byte_array) as a vector of
    // / coefficients and x = pow.
    // /
    // / Mathematically speaking, we define a function `f(E : RLP-encoding) -> F` such that
    // / `f(E) = \sigma_{i = 0}^{len(E) - 1} [byte_to_field_element(coefficients[i]) * pow^(i)]`.
    // /
    // / This function returns:
    // / 1. `f(RLP-encoding(E))`,
    // / 2. `pow^len(RLP-encoding(E))`, which can be seen as the "next" power,
    // / 3. `len(RLP-encoding(coefficients))`, which is necessary for calculating the prefix byte for
    // /    `RLP-encoding(mpt)`.
    // /
    // / Note that, as specified in the function name, we don't actually calculate
    // / `RLP-encoding(byte_array)`.
    // fn calculate_polynomial_emulating_rlp_encoding_cubic(
    //     &mut self,
    //     byte_array: Bytes32Target,
    //     len: U32Target,
    //     pow: U32Target,
    // ) -> (U32Target, U32Target, U32Target) {
    //     let true_v = self._true();
    //     let zero = self.zero_u32();
    //     let one = self.one_u32();
    //     let cons56 = self.constant_u32(56 as u32);

    //     // TODO: It's likely that we'll need to implement the case when the given byte string is
    //     // >= 56 bytes. (e.g., account state) However, for the first iteration, we will only worry
    //     // about the case when the byte string is <= 55 bytes.
    //     let len_lte_55 = self.is_less_than_u32(len, cons56, 32);

    //     self.is_equal(len_lte_55.target, true_v.target);

    //     // There are 2 possible outcomes of encode(byte_array):
    //     //
    //     // 1. len = 1 && byte_array[0] <  0x80  =>  {byte_array[0]}
    //     // 2. else                              =>  {0x80 + len, byte_array[0], byte_array[1], ...}

    //     let cons0x80 = self.constant_u32(128 as u32);

    //     // let first_byte_as_variable = self.byte_to_variable(byte_array[0]);
    //     let first_byte_as_target = byte_array.0[0].to_target(self);
    //     let res_case_1 = U32Target(first_byte_as_target);
    //     let len1 = one;

    //     let mut res_case_2 = self.var_to_cubic(len.variable);
    //     let cons0x80_in_cubic = self.var_to_cubic(cons0x80.variable);
    //     res_case_2 = self.add(res_case_2, cons0x80_in_cubic);

    //     let len2 = self.add(len, one);

    //     let mut next_pow = pow;
    //     for i in 0..ARRAY_LENGTH {
    //         let index = self.constant::<U32Variable>(i as u32);
    //         // let index = self.constant::<U32Variable>(L::Field::from_canonical_usize(i));
    //         // let current_term_in_variable = self.byte_to_variable(byte_array[i]);
    //         let current_term_in_variable = byte_array[i].to_variable(self);
    //         let mut current_term = self.var_to_cubic(current_term_in_variable);

    //         current_term = self.mul(current_term, next_pow);
    //         current_term = self.if_less_than_else(index, len, current_term, zero_cubic);

    //         res_case_2 = self.add(res_case_2, current_term);
    //         let pow_multiplier = self.if_less_than_else(index, len, pow, one_cubic);
    //         next_pow = self.mul(next_pow, pow_multiplier);
    //     }

    //     let is_len_1 = self.is_equal(len, one);
    //     let is_first_variable_less_than_0x80 = self.lt(first_byte_as_u32variable, cons0x80);
    //     let is_case_1 = self.and(is_len_1, is_first_variable_less_than_0x80);

    //     let res_len = self.select(is_case_1, len1, len2);
    //     let res_pow = self.select(is_case_1, pow, next_pow);
    //     let res = self.select(is_case_1, res_case_1, res_case_2);

    //     (res, res_pow, res_len)
    // }

    // / Add in the term corresponding to the prefix byte(s) of the RLP-encoding, given the sum of
    // / the item-wise polynomial.
    // /
    // / The RLP-encoding is in the form of `{ prefix, prefix_0, byte_array_0, prefix_1,
    // / byte_array_1, ... }`. And so far, we have calculated the polynomial for {prefix_0,
    // / byte_array_0, prefix_1, byte_array_1, ...}. Now we have to calculate `prefix`, and
    // / also "shift" the current polynomial. This logic isn't necessarily reusable or modular, but
    // / it's complex logic that blurs out the whole `verify_decoded_mpt_node` function, so this is
    // / a separate function.
    // fn add_prefix_polynomial_and_shift(
    //     &mut self,
    //     sum_of_rlp_encoding_length: U32Variable,
    //     claim_poly: CubicExtensionVariable,
    //     challenge: CubicExtensionVariable,
    // ) -> CubicExtensionVariable {
    //     let true_v = self.constant::<BoolVariable>(true);
    //     let cons56 = self.constant::<U32Variable>(56 as u32);
    //     let cons256 = self.constant::<U32Variable>(256 as u32);
    //     let cons65536 = self.constant::<U32Variable>(65535 as u32);
    //     let cons0xf8 = self.constant::<U32Variable>(248 as u32);
    //     let cons0xf8_in_cubic = self.var_to_cubic(cons0xf8.variable);
    //     let sum_of_rlp_encoding_length_cubic =
    //         self.var_to_cubic(sum_of_rlp_encoding_length.variable);

    //     // Assert that sum_of_rlp_encoding_length is less than 256^2 = 65536 bits. A
    //     // well-formed MPT should never need that many bytes.
    //     let valid_length = self.lt(sum_of_rlp_encoding_length, cons65536);
    //     self.assert_is_equal(true_v, valid_length);

    //     // The main idea is to convert claim_poly into `prefix_term + [appropriate power of
    //     // challenger] * claim_poly`. There are three cases that we work on:
    //     // 1.        combined length <  56    => prefix = {0xc0 + combined length}
    //     // 2.  56 <= combined length <  256   => prefix = {0xf8, combined length in 1 byte}
    //     // 3. 256 <= combined length < 65536  => prefix = {0xf9, combined length in 2 bytes}
    //     //
    //     // RLP technically allows a longer byte string, but we will not implement it, at least, for
    //     // now.

    //     // Case 1: We need 0xc0 + combined_length + claim_poly * challenge.
    //     let mut case_1 = self.constant_cubic(0xc0);
    //     case_1 = self.add(case_1, sum_of_rlp_encoding_length_cubic);
    //     let case_1_poly = self.mul(claim_poly, challenge);
    //     case_1 = self.add(case_1, case_1_poly);

    //     // Case 2: We need 0xf8 + combined_length * challenger + claim_poly * (challenge ^ 2).
    //     let mut case_2 = self.mul(sum_of_rlp_encoding_length_cubic, challenge);
    //     case_2 = self.add(case_2, cons0xf8_in_cubic);
    //     let mut case_2_poly = self.mul(claim_poly, challenge);
    //     case_2_poly = self.mul(case_2_poly, challenge);
    //     case_2 = self.add(case_2, case_2_poly);

    //     // Case 3
    //     //
    //     // Divide sum_of_rlp_encoding_length by cons256 and get the quotient and remainder, and we
    //     // need 0xf9 + div * challenger + rem * (challenger ^ 2) + claim_poly * (challenger ^ 3).
    //     let cons256_in_u32 = self.constant::<U32Variable>(256);

    //     let div_in_u32 = self.div(sum_of_rlp_encoding_length, cons256_in_u32);
    //     let temp_for_rem = self.mul(div_in_u32, cons256_in_u32);
    //     let rem_in_u32 = self.sub(sum_of_rlp_encoding_length, temp_for_rem);

    //     let (mut div, mut rem) = (
    //         self.var_to_cubic(div_in_u32.variable),
    //         self.var_to_cubic(rem_in_u32.variable),
    //     );

    //     let mut case_3 = self.constant_cubic(0xf9);

    //     div = self.mul(div, challenge);
    //     case_3 = self.add(case_3, div);

    //     rem = self.mul(rem, challenge);
    //     rem = self.mul(rem, challenge);
    //     case_3 = self.add(case_3, rem);

    //     let mut case_3_poly = self.mul(claim_poly, challenge);
    //     case_3_poly = self.mul(case_3_poly, challenge);
    //     case_3_poly = self.mul(case_3_poly, challenge);

    //     case_3 = self.add(case_3, case_3_poly);

    //     // Pick the right one.
    //     let mut res = self.if_less_than_else(sum_of_rlp_encoding_length, cons256, case_2, case_3);
    //     res = self.if_less_than_else(sum_of_rlp_encoding_length, cons56, case_1, res);
    //     res
    // }

    // / This function verifies the decoding by comparing the encoded and decoded MPT node.
    // /
    // / Mathematically speaking, we define a function `f(E : RLP-encoding) -> F` such that
    // / `f(E) = \sigma_{i = 0}^{len(E) - 1} [byte_to_field_element(E[i]) * challenger^i]`.
    // /
    // / `verify_decoded_mpt_node` then verifies that `encoded[..len] = rlp-encode(mpt)` by checking
    // / `f(encoded[..len]) = f(rlp-encode(mpt))`.
    // /
    // / `f(encoded[len])` is straightforward. We calculate `f(rlp-encode(mpt))` without explicitly
    // / encoding mpt by calculating:
    // /
    // / - `f(rlp-encode(i-th item in mpt))`` for all `i = 0..(len(mpt) - 1)``, and
    // / - `f(the prefix byte(s) of rlp-encode(mpt))`,
    // /
    // / and combining them using the appropriate power of `challenger`. Of course, we don't
    // / explicitly calculate `rlp-encode(i-th item in mpt)`, either. Instead, we calculate it by
    // / looking at the length and first byte of the `i-th item in mpt`.
    // fn verify_decoded_mpt_node<const ENCODING_LEN: usize>(
    //     &mut self,
    //     encoded: &ArrayVariable<ByteVariable, ENCODING_LEN>,
    //     len: U32Variable,
    //     skip_computation: BoolVariable,
    //     mpt: &MPTVariable,
    // ) {
    //     let mut challenger = RecursiveChallenger::<L::Field, PoseidonHash, D>::new(&mut self.api);

    //     // Give the challenger the encoded string.
    //     challenger.observe_elements(
    //         encoded
    //             .variables()
    //             .iter()
    //             .map(|x| x.0)
    //             .collect::<Vec<_>>()
    //             .as_slice(),
    //     );

    //     challenger.observe_elements(&encoded.variables().iter().map(|x| x.0).collect::<Vec<_>>());

    //     challenger.observe_elements(&encoded.variables().iter().map(|x| x.0).collect::<Vec<_>>());

    //     // challenger.observe_elements(&encoded.variables().iter().map(|x| x.0).collect_vec());
    //     challenger.observe_elements(&len.variables().iter().map(|x| x.0).collect_vec());

    //     // Give the challenger the output of the hint which decodes `encoded`. In other words, this
    //     // is what we're trying to verify. It is ABSOLUTELY essential that we pass in `mpt` here to
    //     // generate challengers as otherwise one can manipulate the polynomial to get 0.
    //     challenger.observe_elements(&mpt.variables().iter().map(|x| x.0).collect_vec());

    //     challenger.observe_elements(
    //         &skip_computation
    //             .variables()
    //             .iter()
    //             .map(|x| x.0)
    //             .collect_vec(),
    //     );

    //     let challenge = CubicExtensionVariable::new(
    //         Variable::from(challenger.get_challenge(&mut self.api)),
    //         Variable::from(challenger.get_challenge(&mut self.api)),
    //         Variable::from(challenger.get_challenge(&mut self.api)),
    //     );

    //     let one = self.one::<CubicExtensionVariable>();
    //     let zero = self.zero::<CubicExtensionVariable>();
    //     let zero_var = self.zero::<U32Variable>();
    //     let true_v = self.constant::<BoolVariable>(true);
    //     let mut encoding_poly = self.zero::<CubicExtensionVariable>();
    //     let mut pow = self.one::<CubicExtensionVariable>();
    //     self.watch(&challenge, "challenge");

    //     for i in 0..ENCODING_LEN {
    //         let current_term_in_variable = encoded[i].to_variable(self);
    //         let mut current_term = self.var_to_cubic(current_term_in_variable);
    //         current_term = self.mul(current_term, pow);
    //         // It's okay to simply add current_term as pow becomes 0 once i = ENCODING_LEN.
    //         encoding_poly = self.add(encoding_poly, current_term);

    //         let index = self.constant::<U32Variable>(i as u32);
    //         let pow_multiplier = self.if_less_than_else(index, len, challenge, zero);
    //         pow = self.mul(pow, pow_multiplier);
    //     }

    //     let mut sum_of_rlp_encoding_length = zero_var;
    //     let mut claim_poly = zero;
    //     pow = one;

    //     let mpt_len = U32Variable::from_variables(self, &[mpt.len]);

    //     for i in 0..MAX_MPT_NODE_SIZE {
    //         let index_i = self.constant::<U32Variable>(i as u32);

    //         let mpt_lens_i = U32Variable::from_variables(self, &[mpt.lens[i]]);
    //         let (mut poly, mut next_pow, mut encoding_len) = self
    //             .calculate_polynomial_emulating_rlp_encoding_cubic(
    //                 &mpt.data[i],
    //                 mpt_lens_i,
    //                 challenge,
    //             );

    //         // Shift the `poly` value by the appropriate power of `challenger`, and also check
    //         // if we should even include this.
    //         poly = self.if_less_than_else(index_i, mpt_len, poly, zero);
    //         poly = self.mul(poly, pow);
    //         claim_poly = self.add(claim_poly, poly);

    //         next_pow = self.if_less_than_else(index_i, mpt_len, next_pow, one);
    //         pow = self.mul(pow, next_pow);

    //         encoding_len = self.if_less_than_else(index_i, mpt_len, encoding_len, zero_var);
    //         sum_of_rlp_encoding_length = self.add(sum_of_rlp_encoding_length, encoding_len);
    //     }
    //     claim_poly =
    //         self.add_prefix_polynomial_and_shift(sum_of_rlp_encoding_length, claim_poly, challenge);
    //     self.watch(&claim_poly, "claim_poly");
    //     self.watch(&encoding_poly, "encoding_poly");
    //     let claim_poly_equals_encoding_poly = self.is_equal(claim_poly, encoding_poly);
    //     let result = self.or(skip_computation, claim_poly_equals_encoding_poly);

    //     self.assert_is_equal(result, true_v);
    // }

    // fn decode_mpt_node<const ENCODING_LEN: usize, const ELEMENT_LEN: usize>(
    //     &mut self,
    //     encoded: ArrayVariable<ByteVariable, ENCODING_LEN>,
    //     len: Variable,
    //     skip_computation: BoolVariable,
    // ) -> MPTVariable {
    //     let mut input_stream = VariableStream::new();
    //     input_stream.write(&encoded);
    //     input_stream.write(&len);
    //     input_stream.write(&skip_computation);

    //     let hint = DecodeHint::<ENCODING_LEN> {};

    //     let output_stream = self.hint(input_stream, hint);
    //     let decoded_node = output_stream.read::<MPTVariable>(self);
    //     let len_u32 = U32Variable::from_variables(self, &[len]);

    //     self.verify_decoded_mpt_node::<ENCODING_LEN>(
    //         &encoded,
    //         len_u32,
    //         skip_computation,
    //         &decoded_node,
    //     );

    //     decoded_node
    // }
}
