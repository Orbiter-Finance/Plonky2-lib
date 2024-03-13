use crate::types::bytes::ByteTarget;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::U32Target;

pub fn subarray_equal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &[ByteTarget],
    a_offset: U32Target,
    b: &[ByteTarget],
    b_offset: U32Target,
    len: U32Target,
) -> BoolTarget {
    todo!();
}
