use std::marker::PhantomData;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CommonCircuitData},
    util::serialization::{Buffer, IoResult, Read, Write},
};
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};

use crate::watchers::target_watcher::TargetWatcher;

extern crate hex;

#[macro_export]
macro_rules! bytes {
    ($hex_literal:expr) => {{
        let hex_string = $hex_literal;
        let stripped = if let Some(stripped) = hex_string.strip_prefix("0x") {
            stripped
        } else {
            &hex_string
        };
        hex::decode(stripped)
            .expect("Invalid hex string")
            .try_into()
            .expect(&format!(
                "Wrong byte length {} for hex string {}",
                stripped.len(),
                hex_string
            ))
    }};
}

pub trait CircuitBuilderU32Ext<F: RichField + Extendable<D>, const D: usize>:
    CircuitBuilderU32<F, D>
{
    fn from_target_to_u32_safe(&mut self, target: Target) -> U32Target;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderU32Ext<F, D>
    for CircuitBuilder<F, D>
{
    fn from_target_to_u32_safe(&mut self, target: Target) -> U32Target {
        let const_u32_max = self.constant(F::from_canonical_u64(1 << 32));
        let quotient = self.add_virtual_target();
        let rem = self.add_virtual_target();

        let generator = U32DivRemGenerator {
            numerator: target.clone(),
            denominator: const_u32_max.clone(),
            quotient: quotient.clone(),
            rem: rem.clone(),
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);

        let tmp = self.mul(quotient, const_u32_max);
        let tmp2 = self.add(rem, tmp);

        // self.le
        // TODO: should we constrain rem < const_u32_max?
        self.connect(tmp2, target);

        U32Target(rem)
    }
}

#[derive(Debug, Default)]
pub struct U32DivRemGenerator<F: RichField + Extendable<D>, const D: usize> {
    // we directly use Target here so that this structure can be used in from_target_to_u32_safe
    // we need a way to calculate the target value in integer division
    numerator: Target,
    denominator: Target,
    quotient: Target,
    rem: Target,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for U32DivRemGenerator<F, D>
{
    fn id(&self) -> String {
        "U32DivRemGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        let deps = vec![self.numerator, self.denominator];
        deps
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let num = witness.get_target(self.numerator).to_canonical_u64();
        let dem = witness.get_target(self.denominator).to_canonical_u64();
        let quotient = num / dem;
        let rem = num % dem;
        out_buffer.set_target(self.quotient, F::from_canonical_u64(quotient));
        out_buffer.set_target(self.rem, F::from_canonical_u64(rem));
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target(self.numerator)?;
        dst.write_target(self.denominator)?;
        dst.write_target(self.quotient)?;
        dst.write_target(self.rem)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let numerator = src.read_target()?;
        let denominator = src.read_target()?;
        let quotient = src.read_target()?;
        let rem = src.read_target()?;
        Ok(Self {
            numerator,
            denominator,
            quotient,
            rem,
            _phantom: PhantomData,
        })
    }
}
