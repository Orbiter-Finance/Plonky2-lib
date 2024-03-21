use plonky2::field::extension::quadratic::QuadraticExtension;
use plonky2::field::goldilocks_field::GoldilocksField;

use core::fmt::Debug;
use log::info;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::{HashOut, HashOutTarget, RichField};
use plonky2::hash::hashing::{compress, hash_n_to_hash_no_pad, PlonkyPermutation};
use plonky2::hash::poseidon::{PoseidonHash, SPONGE_RATE};
use plonky2::hash::poseidon::{PoseidonPermutation, SPONGE_WIDTH};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, Hasher};
use poseidon_permutation::bindings::permute;

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct PoseidonBN128Permutation<F> {
    state: [F; SPONGE_WIDTH],
}

impl<F: Eq> Eq for PoseidonBN128Permutation<F> {}

impl<F> AsRef<[F]> for PoseidonBN128Permutation<F> {
    fn as_ref(&self) -> &[F] {
        &self.state
    }
}

impl<F: RichField + Copy + Debug + Default + Eq + Send + Sync> PlonkyPermutation<F>
    for PoseidonBN128Permutation<F>
{
    fn permute(&mut self) {
        assert_eq!(SPONGE_WIDTH, 12);
        unsafe {
            let h = permute(
                self.state[0].to_canonical_u64(),
                self.state[1].to_canonical_u64(),
                self.state[2].to_canonical_u64(),
                self.state[3].to_canonical_u64(),
                self.state[4].to_canonical_u64(),
                self.state[5].to_canonical_u64(),
                self.state[6].to_canonical_u64(),
                self.state[7].to_canonical_u64(),
                self.state[8].to_canonical_u64(),
                self.state[9].to_canonical_u64(),
                self.state[10].to_canonical_u64(),
                self.state[11].to_canonical_u64(),
            );
            self.state = [
                F::from_canonical_u64(if h.r0 >= F::ORDER {
                    h.r0 - F::ORDER
                } else {
                    h.r0
                }),
                F::from_canonical_u64(if h.r1 >= F::ORDER {
                    h.r1 - F::ORDER
                } else {
                    h.r1
                }),
                F::from_canonical_u64(if h.r2 >= F::ORDER {
                    h.r2 - F::ORDER
                } else {
                    h.r2
                }),
                F::from_canonical_u64(if h.r3 >= F::ORDER {
                    h.r3 - F::ORDER
                } else {
                    h.r3
                }),
                F::from_canonical_u64(if h.r4 >= F::ORDER {
                    h.r4 - F::ORDER
                } else {
                    h.r4
                }),
                F::from_canonical_u64(if h.r5 >= F::ORDER {
                    h.r5 - F::ORDER
                } else {
                    h.r5
                }),
                F::from_canonical_u64(if h.r6 >= F::ORDER {
                    h.r6 - F::ORDER
                } else {
                    h.r6
                }),
                F::from_canonical_u64(if h.r7 >= F::ORDER {
                    h.r7 - F::ORDER
                } else {
                    h.r7
                }),
                F::from_canonical_u64(if h.r8 >= F::ORDER {
                    h.r8 - F::ORDER
                } else {
                    h.r8
                }),
                F::from_canonical_u64(if h.r9 >= F::ORDER {
                    h.r9 - F::ORDER
                } else {
                    h.r9
                }),
                F::from_canonical_u64(if h.r10 >= F::ORDER {
                    h.r10 - F::ORDER
                } else {
                    h.r10
                }),
                F::from_canonical_u64(if h.r11 >= F::ORDER {
                    h.r11 - F::ORDER
                } else {
                    h.r11
                }),
            ];
        }
    }

    const RATE: usize = SPONGE_RATE;

    const WIDTH: usize = SPONGE_WIDTH;

    fn new<I: IntoIterator<Item = F>>(iter: I) -> Self {
        let mut perm = Self {
            state: [F::default(); SPONGE_WIDTH],
        };
        perm.set_from_iter(iter, 0);
        perm
    }

    fn set_elt(&mut self, elt: F, idx: usize) {
        self.state[idx] = elt;
    }

    fn set_from_iter<I: IntoIterator<Item = F>>(&mut self, elts: I, start_idx: usize) {
        for (s, e) in self.state[start_idx..].iter_mut().zip(elts) {
            *s = e;
        }
    }

    fn set_from_slice(&mut self, elts: &[F], start_idx: usize) {
        let begin = start_idx;
        let end = start_idx + elts.len();
        self.state[begin..end].copy_from_slice(elts);
    }

    fn squeeze(&self) -> &[F] {
        &self.state[..Self::RATE]
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct PoseidonBN128Hash;
impl<F: RichField> Hasher<F> for PoseidonBN128Hash {
    const HASH_SIZE: usize = 4 * 8;
    type Hash = HashOut<F>;
    type Permutation = PoseidonBN128Permutation<F>;

    fn hash_no_pad(input: &[F]) -> Self::Hash {
        hash_n_to_hash_no_pad::<F, Self::Permutation>(input)
    }

    fn two_to_one(left: Self::Hash, right: Self::Hash) -> Self::Hash {
        compress::<F, Self::Permutation>(left, right)
    }

    fn hash_public_inputs(input: &[F]) -> Self::Hash {
        PoseidonHash::hash_no_pad(input)
    }
}

// TODO: this is a work around. Still use Goldilocks based Poseidon for algebraic PoseidonBN128Hash.
impl<F: RichField> AlgebraicHasher<F> for PoseidonBN128Hash {
    type AlgebraicPermutation = PoseidonPermutation<Target>;

    fn permute_swapped<const D: usize>(
        inputs: Self::AlgebraicPermutation,
        swap: BoolTarget,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self::AlgebraicPermutation
    where
        F: RichField + Extendable<D>,
    {
        PoseidonHash::permute_swapped(inputs, swap, builder)
    }

    fn public_inputs_hash<const D: usize>(
        inputs: Vec<Target>,
        builder: &mut CircuitBuilder<F, D>,
    ) -> HashOutTarget
    where
        F: RichField + Extendable<D>,
    {
        PoseidonHash::public_inputs_hash(inputs, builder)
    }
}

/// Configuration using Poseidon over the Goldilocks field.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct PoseidonBN128GoldilocksConfig;

impl GenericConfig<2> for PoseidonBN128GoldilocksConfig {
    type F = GoldilocksField;
    type FE = QuadraticExtension<Self::F>;
    type Hasher = PoseidonBN128Hash;
    type InnerHasher = PoseidonBN128Hash;
}
