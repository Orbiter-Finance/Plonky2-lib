use crate::nonnative::biguint::BigUintTarget;
use array_macro::array;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

#[derive(Debug, Clone, Copy)]
pub struct ByteTarget(pub [BoolTarget; 8]);

impl ByteTarget {
    pub fn from_u32<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        value: u32,
    ) -> Self {
        let target = builder.constant(F::from_canonical_u32(value));
        builder.low_bits(target, 8, 8).try_into().unwrap()
    }

    pub fn as_be_bits(self) -> [BoolTarget; 8] {
        self.0
    }

    pub fn to_nibbles<F: RichField + Extendable<D>, const D: usize>(
        self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> [ByteTarget; 2] {
        let bits = self.as_be_bits();

        let mut left_nibble = array![_ => builder.constant_bool(false); 8];
        left_nibble[4..].copy_from_slice(&bits[0..4]);

        let mut right_nibble = array![_ => builder.constant_bool(false); 8];
        right_nibble[4..].copy_from_slice(&bits[4..8]);

        [ByteTarget(left_nibble), ByteTarget(right_nibble)]
    }
}

impl From<Vec<BoolTarget>> for ByteTarget {
    fn from(vec: Vec<BoolTarget>) -> Self {
        let array: [BoolTarget; 8] = vec.try_into().expect("Vec length is not 8");
        ByteTarget(array)
    }
}

/// A variable in the circuit representing a fixed length array of variables.
/// We use this to avoid stack overflow arrays associated with fixed-length arrays.
#[derive(Debug, Clone)]
pub struct BytesTarget<const N: usize> {
    pub data: Vec<ByteTarget>,
}

impl<const N: usize> BytesTarget<N> {
    pub fn new(elements: Vec<ByteTarget>) -> Self {
        assert_eq!(elements.len(), N);
        Self { data: elements }
    }

    pub fn as_slice(&self) -> &[ByteTarget] {
        &self.data
    }

    pub fn as_vec(&self) -> Vec<ByteTarget> {
        self.data.clone()
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.data.len()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Bytes32Target(pub [ByteTarget; 32]);

impl Bytes32Target {
    pub fn from_biguint_target<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        value: BigUintTarget,
    ) -> Self {
        let mut bytes32 = Vec::with_capacity(32);
        for limb in value.limbs.iter() {
            let byte: ByteTarget = builder.low_bits(limb.0, 8, 8).try_into().unwrap();
            bytes32.push(byte);
        }

        bytes32.try_into().unwrap()
    }

    pub fn as_bytes(&self) -> [ByteTarget; 32] {
        self.0
    }
}

impl From<Vec<ByteTarget>> for Bytes32Target {
    fn from(vec: Vec<ByteTarget>) -> Self {
        let array: [ByteTarget; 32] = vec.try_into().expect("Vec length is not 8");
        Bytes32Target(array)
    }
}

pub trait Nibbles<ByteTarget> {
    fn to_nibbles<F: RichField + Extendable<D>, const D: usize>(
        self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Vec<ByteTarget>;
}

impl Nibbles<ByteTarget> for Vec<ByteTarget> {
    fn to_nibbles<F: RichField + Extendable<D>, const D: usize>(
        self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Vec<ByteTarget> {
        self.iter()
            .flat_map(|b| b.to_nibbles(builder))
            .collect::<Vec<ByteTarget>>()
    }
}
