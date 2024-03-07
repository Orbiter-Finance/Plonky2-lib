use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};

/// The less than or equal operation (<=).
///
/// Types implementing this trait can be used within the `builder.lte(lhs, rhs)` method.
pub fn less_than_equal_u32<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    lhs: U32Target,
    rhs: U32Target,
) -> BoolTarget {
    let lte = builder.is_less_than_u32(rhs, lhs, 32);
    builder.not(lte)
}
