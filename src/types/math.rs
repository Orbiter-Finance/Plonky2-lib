use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use plonky2_u32::gadgets::multiple_comparison::list_le_circuit;

/// The less than or equal operation (<=).
///
/// Types implementing this trait can be used within the `builder.lte(lhs, rhs)` method.
pub trait LessThanOrEqual<F: RichField + Extendable<D>, const D: usize, Rhs = Self> {
    fn lte(self, rhs: Rhs, builder: &mut CircuitBuilder<F, D>) -> BoolTarget;
}

impl<F: RichField + Extendable<D>, const D: usize> LessThanOrEqual<F, D> for U32Target {
    fn lte(self, rhs: Self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        list_le_circuit(builder, vec![self.0], vec![rhs.0], 32).into()
    }
}

pub fn lt<F: RichField + Extendable<D>, const D: usize, Lhs, Rhs>(
    builder: &mut CircuitBuilder<F, D>,
    lhs: Lhs,
    rhs: Rhs,
) -> BoolTarget
where
    Rhs: LessThanOrEqual<F, D, Lhs>,
{
    let lte = rhs.lte(lhs, builder);
    builder.not(lte)
}
