use crate::nonnative::biguint::BigUintTarget;
use array_macro::array;
use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::U32Target;

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

    pub fn as_le_bits(self) -> [BoolTarget; 8] {
        let mut bits = self.as_be_bits();
        bits.reverse();
        bits
    }

    pub fn targets(&self) -> Vec<Target> {
        self.as_be_bits().iter().map(|v| v.target).collect()
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

    pub fn is_equal<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: ByteTarget,
    ) -> BoolTarget {
        let mut result = builder._true();
        for (t1, t2) in self.targets().iter().zip(other.targets().iter()) {
            let target_eq = builder.is_equal(*t1, *t2);
            result = builder.and(target_eq, result);
        }
        result
    }

    pub fn select<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        selector: BoolTarget,
        i2: ByteTarget,
    ) -> ByteTarget {
        assert_eq!(self.targets().len(), i2.targets().len());
        let mut targets = Vec::new();
        for (t1, t2) in self.targets().iter().zip(i2.targets().iter()) {
            targets.push(BoolTarget::new_unsafe(builder.select(selector, *t1, *t2)));
        }
        targets.try_into().unwrap()
    }

    /// Creates a Target from a ByteTarget.
    pub fn to_target<F: RichField + Extendable<D>, const D: usize>(
        self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Target {
        let le_targets = self.as_le_bits();
        builder.le_sum(le_targets.into_iter())
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

    pub fn from_biguint_target<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        value: BigUintTarget,
    ) -> Self {
        let mut bytes = Vec::with_capacity(N);
        for limb in value.limbs.iter() {
            let byte: ByteTarget = builder.low_bits(limb.0, 8, 8).try_into().unwrap();
            bytes.push(byte);
        }
        Self::new(bytes)
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

    pub fn select_array<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        selector: Target,
    ) -> ByteTarget {
        let array = self.as_slice();
        // The accumulator holds the variable of the selected result
        let mut accumulator = array[0].clone();

        for i in 0..array.len() {
            // Whether the accumulator should be set to the i-th element (if selector_enabled=true)
            // Or should be set to the previous value (if selector_enabled=false)
            let target_i = builder.constant(F::from_canonical_usize(i));
            let selector_enabled = builder.is_equal(target_i, selector);
            // If selector_enabled, then accum_var gets set to arr_var, otherwise it stays the same
            accumulator = array[i].select(builder, selector_enabled, accumulator);
        }

        accumulator
    }

    pub fn to_bytes32_target(self) -> Bytes32Target {
        assert_eq!(N, 32);
        self.data.try_into().unwrap()
    }
}

impl<const N: usize> From<Vec<ByteTarget>> for BytesTarget<N> {
    fn from(elements: Vec<ByteTarget>) -> Self {
        BytesTarget::new(elements)
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

    pub fn targets(&self) -> Vec<Target> {
        self.as_bytes().iter().flat_map(|v| v.targets()).collect()
    }

    pub fn is_equal<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: Bytes32Target,
    ) -> BoolTarget {
        let mut result = builder._true();
        for (t1, t2) in self.targets().iter().zip(other.targets().iter()) {
            let target_eq = builder.is_equal(*t1, *t2);
            result = builder.and(target_eq, result);
        }
        result
    }

    pub fn select<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        selector: BoolTarget,
        i2: Bytes32Target,
    ) -> Bytes32Target {
        assert_eq!(self.targets().len(), i2.targets().len());
        let mut targets = Vec::new();
        for (t1, t2) in self.targets().iter().zip(i2.targets().iter()) {
            targets.push(BoolTarget::new_unsafe(builder.select(selector, *t1, *t2)));
        }
        targets.try_into().unwrap()
    }
}

impl From<Vec<ByteTarget>> for Bytes32Target {
    fn from(vec: Vec<ByteTarget>) -> Self {
        let array: [ByteTarget; 32] = vec.try_into().expect("Vec length is not 8");
        Bytes32Target(array)
    }
}

impl From<Vec<BoolTarget>> for Bytes32Target {
    fn from(vec: Vec<BoolTarget>) -> Self {
        let array: Vec<ByteTarget> = vec
            .as_slice()
            .chunks(8)
            .map(|v| {
                let byte: ByteTarget = v.to_vec().try_into().expect("Vec length is not 8");
                byte
            })
            .collect();
        array.try_into().unwrap()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Bytes32ArrayTarget<const N: usize>(pub [Bytes32Target; N]);

impl<const N: usize> Bytes32ArrayTarget<N> {
    pub fn new(elements: Vec<Bytes32Target>) -> Self {
        assert_eq!(elements.len(), N);
        elements.try_into().unwrap()
    }
    pub fn as_slice(&self) -> &[Bytes32Target] {
        self.0.as_slice()
    }

    pub fn select_array<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        selector: Target,
    ) -> Bytes32Target {
        let array = self.as_slice();
        // The accumulator holds the variable of the selected result
        let mut accumulator = array[0].clone();

        for i in 0..array.len() {
            // Whether the accumulator should be set to the i-th element (if selector_enabled=true)
            // Or should be set to the previous value (if selector_enabled=false)
            let target_i = builder.constant(F::from_canonical_usize(i));
            let selector_enabled = builder.is_equal(target_i, selector);
            // If selector_enabled, then accum_var gets set to arr_var, otherwise it stays the same
            accumulator = array[i].select(builder, selector_enabled, accumulator);
        }

        accumulator
    }
}

impl<const N: usize> From<Vec<Bytes32Target>> for Bytes32ArrayTarget<N> {
    fn from(vec: Vec<Bytes32Target>) -> Self {
        let array: [Bytes32Target; N] = vec.try_into().expect("Vec length is not 8");
        Bytes32ArrayTarget(array)
    }
}

#[derive(Debug, Clone)]
pub struct ArrayTarget<const N: usize>(pub [Target; N]);

impl<const N: usize> ArrayTarget<N> {
    pub fn new() -> Self {
        todo!()
    }

    pub fn targets(&self) -> Vec<Target> {
        self.0.to_vec()
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
