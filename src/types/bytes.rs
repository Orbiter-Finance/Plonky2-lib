use crate::nonnative::biguint::{BigUintTarget, GeneratedValuesBigUint};
use array_macro::array;
use itertools::Itertools;
use num::BigUint;
use plonky2::field::extension::Extendable;
use plonky2::field::types::{PrimeField, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::GeneratedValues;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};
use plonky2_u32::witness::WitnessU32;

/// A Target in the circuit representing a byte value. Under the hood, it is represented as
/// eight bits stored in big endian.
#[derive(Debug, Clone, Copy)]
pub struct ByteTarget(pub [BoolTarget; 8]);

impl ByteTarget {
    pub fn from_u8<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        value: u32,
    ) -> Self {
        let target = builder.constant(F::from_canonical_u8(value as u8));
        Self::from_target(builder, target)
    }

    /// Creates a ByteTarget from a Target.
    pub fn from_target<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        target: Target,
    ) -> Self {
        builder.range_check(target, 8);
        let bools = builder.low_bits(target, 8, 8);
        Self::from_bool_targets(bools)
    }

    /// Create a ByteTarget from a BoolTarget array of length 8.
    pub fn from_bool_targets(mut targets: Vec<BoolTarget>) -> Self {
        assert_eq!(targets.len(), 8);
        targets.reverse();
        targets.try_into().unwrap()
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
        let targets = value
            .limbs
            .into_iter()
            .map(|t| t.0)
            .collect::<Vec<Target>>();
        Self::from_targets(builder, targets)
    }

    /// Create a BytesTarget from a Target array
    pub fn from_targets<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        targets: Vec<Target>,
    ) -> Self {
        let mut bytes = Vec::with_capacity(N);
        for target in targets.into_iter() {
            let byte = ByteTarget::from_target(builder, target);
            bytes.push(byte);
        }
        Self::new(bytes)
    }

    pub fn from_bool_targets(targets: Vec<BoolTarget>) -> Self {
        let size = 8;
        assert_eq!(targets.len() % size, 0);
        let byte_targets = targets
            .chunks_exact(size)
            .map(|v| ByteTarget::from_bool_targets(v.to_vec()))
            .collect_vec();

        Self::new(byte_targets)
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
        let targets = value
            .limbs
            .into_iter()
            .map(|t| t.0)
            .collect::<Vec<Target>>();
        Self::from_targets(builder, targets)
    }

    pub fn from_targets<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        targets: Vec<Target>,
    ) -> Self {
        BytesTarget::<32>::from_targets(builder, targets).to_bytes32_target()
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
        let array: [ByteTarget; 32] = vec.try_into().expect("Vec length is not 32");
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
        let array: [Bytes32Target; N] = vec.try_into().unwrap();
        Bytes32ArrayTarget(array)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct U32ArrayTarget<const N: usize>(pub [U32Target; N]);

impl<const N: usize> U32ArrayTarget<N> {
    pub fn new() -> Self {
        todo!()
    }

    pub fn targets(&self) -> Vec<U32Target> {
        self.0.to_vec()
    }
}

impl<const N: usize> From<Vec<U32Target>> for U32ArrayTarget<N> {
    fn from(vec: Vec<U32Target>) -> Self {
        let array: [U32Target; N] = vec.try_into().unwrap();
        U32ArrayTarget(array)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct U256Target(pub [U32Target; 8]);

impl From<Vec<U32Target>> for U256Target {
    fn from(vec: Vec<U32Target>) -> Self {
        let array: [U32Target; 8] = vec.try_into().expect("Vec length is not 8");
        U256Target(array)
    }
}

#[derive(Debug, Clone)]
pub struct AddressTarget(pub BytesTarget<20>);

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

pub trait CircuitBuilderBytes<F: RichField + Extendable<D>, const D: usize> {
    fn add_virtual_byte_target(&mut self) -> ByteTarget;

    fn add_virtual_bytes_target<const N: usize>(&mut self) -> BytesTarget<N>;

    fn add_virtual_bytes32_target(&mut self) -> Bytes32Target;

    fn add_virtual_bytes32_array_target<const N: usize>(&mut self) -> Bytes32ArrayTarget<N>;

    fn add_virtual_u32_array_target<const N: usize>(&mut self) -> U32ArrayTarget<N>;

    fn add_virtual_u256_target(&mut self) -> U256Target;

    fn assert_bytes32_is_equal(&mut self, x: Bytes32Target, y: Bytes32Target);
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderBytes<F, D>
    for CircuitBuilder<F, D>
{
    fn add_virtual_byte_target(&mut self) -> ByteTarget {
        let bool_targets: Vec<_> = (0..8)
            .map(|_| self.add_virtual_bool_target_unsafe())
            .collect();
        bool_targets.into()
    }

    fn add_virtual_bytes_target<const N: usize>(&mut self) -> BytesTarget<N> {
        let byte_targets: Vec<_> = (0..N).map(|_| self.add_virtual_byte_target()).collect();
        byte_targets.into()
    }

    fn add_virtual_bytes32_target(&mut self) -> Bytes32Target {
        let byte_targets: Vec<_> = (0..32).map(|_| self.add_virtual_byte_target()).collect();
        byte_targets.into()
    }

    fn add_virtual_bytes32_array_target<const N: usize>(&mut self) -> Bytes32ArrayTarget<N> {
        let byte32_targets: Vec<_> = (0..N).map(|_| self.add_virtual_bytes32_target()).collect();
        byte32_targets.into()
    }

    fn add_virtual_u32_array_target<const N: usize>(&mut self) -> U32ArrayTarget<N> {
        let u32_targets = self.add_virtual_u32_targets(N);
        u32_targets.into()
    }

    fn add_virtual_u256_target(&mut self) -> U256Target {
        let u32_targets = self.add_virtual_u32_targets(8);
        u32_targets.into()
    }

    fn assert_bytes32_is_equal(&mut self, x: Bytes32Target, y: Bytes32Target) {
        for (t1, t2) in x.targets().iter().zip(y.targets().iter()) {
            self.connect(*t1, *t2);
        }
    }
}

pub trait WitnessBytes<F: PrimeField64>: Witness<F> {
    fn set_byte_target(&mut self, target: &ByteTarget, value: u32);

    fn get_byte_target(&self, target: ByteTarget) -> u32;

    fn set_bytes_target<const N: usize>(&mut self, target: &BytesTarget<N>, value: Vec<u32>);

    fn get_bytes_target<const N: usize>(&self, target: BytesTarget<N>) -> Vec<u32>;

    fn set_bytes32_target(&mut self, target: &Bytes32Target, value: Vec<u32>);

    fn get_bytes32_target(&self, target: Bytes32Target) -> Vec<u32>;

    fn set_bytes32_array_target<const N: usize>(
        &mut self,
        target: &Bytes32ArrayTarget<N>,
        value: Vec<Vec<u32>>,
    );

    fn set_u32_array_target<const N: usize>(&mut self, target: &U32ArrayTarget<N>, value: Vec<u32>);

    fn set_u256_target(&mut self, target: &U256Target, value: Vec<u32>);
}

impl<T: Witness<F>, F: PrimeField64> WitnessBytes<F> for T {
    fn set_byte_target(&mut self, target: &ByteTarget, value: u32) {
        let bools = u32_to_bools(value);
        assert_eq!(target.as_be_bits().len(), bools.len());
        for (i, &bool) in bools.iter().enumerate() {
            self.set_bool_target(target.as_be_bits()[i], bool);
        }
    }

    fn get_byte_target(&self, target: ByteTarget) -> u32 {
        let target_values: Vec<_> = target
            .as_be_bits()
            .into_iter()
            .map(|t| self.get_bool_target(t))
            .collect();
        bools_to_u32(target_values)
    }

    fn set_bytes_target<const N: usize>(&mut self, target: &BytesTarget<N>, value: Vec<u32>) {
        assert_eq!(N, value.len());
        for (u, t) in value.iter().zip(target.as_vec().iter()) {
            self.set_byte_target(t, *u);
        }
    }

    fn get_bytes_target<const N: usize>(&self, target: BytesTarget<N>) -> Vec<u32> {
        let values: Vec<_> = target
            .as_vec()
            .into_iter()
            .map(|t| self.get_byte_target(t))
            .collect();
        values
    }

    fn set_bytes32_target(&mut self, target: &Bytes32Target, value: Vec<u32>) {
        assert_eq!(32, value.len());
        for (u, t) in value.iter().zip(target.as_bytes().iter()) {
            self.set_byte_target(t, *u);
        }
    }

    fn get_bytes32_target(&self, target: Bytes32Target) -> Vec<u32> {
        let values: Vec<_> = target
            .as_bytes()
            .into_iter()
            .map(|t| self.get_byte_target(t))
            .collect();
        values
    }

    fn set_bytes32_array_target<const N: usize>(
        &mut self,
        target: &Bytes32ArrayTarget<N>,
        value: Vec<Vec<u32>>,
    ) {
        assert_eq!(N, value.len());
        for (u, t) in value.iter().zip(target.as_slice().iter()) {
            self.set_bytes32_target(t, u.clone());
        }
    }

    fn set_u32_array_target<const N: usize>(
        &mut self,
        target: &U32ArrayTarget<N>,
        value: Vec<u32>,
    ) {
        assert_eq!(N, value.len());
        for (u, t) in value.iter().zip(target.0.iter()) {
            self.set_u32_target(*t, *u);
        }
    }

    fn set_u256_target(&mut self, target: &U256Target, value: Vec<u32>) {
        assert_eq!(8, value.len());
        for (u, t) in value.iter().zip(target.0.iter()) {
            self.set_u32_target(*t, *u);
        }
    }
}

/// GeneratedValues

pub trait GeneratedValuesBytes<F: PrimeField> {
    fn set_byte_target(&mut self, target: &ByteTarget, value: u32);
    fn set_bytes32_target(&mut self, target: &Bytes32Target, value: Vec<u32>);
}

impl<F: PrimeField> GeneratedValuesBytes<F> for GeneratedValues<F> {
    fn set_byte_target(&mut self, target: &ByteTarget, value: u32) {
        let bools = u32_to_bools(value);
        assert_eq!(target.as_be_bits().len(), bools.len());
        for (i, &bool) in bools.iter().enumerate() {
            self.set_bool_target(target.as_be_bits()[i], bool);
        }
    }
    fn set_bytes32_target(&mut self, target: &Bytes32Target, value: Vec<u32>) {
        assert_eq!(32, value.len());
        for (u, t) in value.iter().zip(target.as_bytes().iter()) {
            self.set_byte_target(t, *u);
        }
    }
}

pub fn u32_to_bools(mut value: u32) -> Vec<bool> {
    let mut binary: Vec<bool> = Vec::new();
    while value > 0 {
        binary.insert(0, if value & 1 == 1 { true } else { false });
        value >>= 1;
    }
    while binary.len() < 8 {
        binary.insert(0, false);
    }
    binary
}

pub fn bools_to_u32(bools: Vec<bool>) -> u32 {
    let mut value: u32 = 0;
    for &b in bools.iter() {
        value <<= 1;
        if b {
            value |= 1;
        }
    }
    value
}
