use std::marker::PhantomData;

use log::{log, Level};
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{self, Target};
use plonky2::iop::witness::{PartitionWitness, Witness};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{IoResult, Read, Write};

use crate::types::bytes::ByteTarget;

// use super::CircuitBuilder;
// use crate::backend::circuit::PlonkParameters;
// use crate::prelude::CircuitVariable;

pub trait TargetWatcher<F: RichField + Extendable<D>, const D: usize> {
    fn watch(&mut self, target: &Target, log: &str);

    fn watch_with_level(&mut self, target: &Target, log: &str, log_level: Level);

    fn watch_slice(&mut self, targets: &[Target], log: &str);

    fn watch_slice_with_level(&mut self, targets: &[Target], log: &str, log_level: Level);
}

impl<F: RichField + Extendable<D>, const D: usize> TargetWatcher<F, D> for CircuitBuilder<F, D> {
    fn watch(&mut self, target: &Target, log: &str) {
        let target = target.clone();
        let log = String::from(log);

        let generator: TargetWatchGenerator<F, D> = TargetWatchGenerator {
            targets: vec![target],
            log,
            log_level: Level::Info,
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);
    }

    fn watch_with_level(&mut self, target: &Target, log: &str, log_level: Level) {
        let target = target.clone();
        let log = String::from(log);

        let generator: TargetWatchGenerator<F, D> = TargetWatchGenerator {
            targets: vec![target],
            log,
            log_level,
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);
    }

    fn watch_slice(&mut self, targets: &[Target], log: &str) {
        let targets = targets.to_vec();
        let log = String::from(log);

        let generator: TargetWatchGenerator<F, D> = TargetWatchGenerator {
            targets,
            log,
            log_level: Level::Info,
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);
    }

    fn watch_slice_with_level(&mut self, targets: &[Target], log: &str, log_level: Level) {
        let targets = targets.to_vec();
        let log = String::from(log);

        let generator: TargetWatchGenerator<F, D> = TargetWatchGenerator {
            targets,
            log,
            log_level,
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);
    }
}

#[derive(Debug, Clone)]
pub struct TargetWatchGenerator<F: RichField, const D: usize> {
    pub targets: Vec<Target>,
    pub log: String,
    pub log_level: Level,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> TargetWatchGenerator<F, D> {
    pub fn id() -> String {
        format!("WatchGenerator")
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for TargetWatchGenerator<F, D>
{
    fn id(&self) -> String {
        Self::id()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.targets.clone()
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        let log_bytes = self.log.as_bytes();
        dst.write_usize(log_bytes.len())?;
        dst.write_all(log_bytes)?;

        let log_level_num = match self.log_level {
            Level::Trace => 1,
            Level::Debug => 2,
            Level::Info => 3,
            Level::Warn => 4,
            Level::Error => 5,
        };
        dst.write_usize(log_level_num)?;

        dst.write_usize(self.targets.len())?;
        self.targets.iter().try_for_each(|v| dst.write_target(*v))
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        let log_size = src.read_usize()?;
        let mut log_bytes = vec![0u8; log_size];
        src.read_exact(&mut log_bytes)?;
        let log = String::from_utf8(log_bytes).unwrap();

        let log_num = src.read_usize()?;
        let log_level = match log_num {
            1 => Level::Trace,
            2 => Level::Debug,
            3 => Level::Info,
            4 => Level::Warn,
            5 => Level::Error,
            _ => panic!("Invalid log level"),
        };

        let variables_len = src.read_usize()?;
        let mut targets = Vec::new();

        for i in 0..variables_len {
            let target = src.read_target()?;
            targets.push(target);
        }

        Ok(Self {
            targets,
            log,
            log_level,
            _phantom: PhantomData,
        })
    }

    fn run_once(&self, witness: &PartitionWitness<F>, _out_buffer: &mut GeneratedValues<F>) {
        let values: Vec<F> = self
            .targets
            .iter()
            .flat_map(|x| witness.try_get_target(*x))
            .collect();
        let formatted_log = if values.len() == 1 {
            format!("[Watch] {}: {:?}", self.log, values[0])
        } else {
            format!("[Watch] {}: {:?}", self.log, values)
        };
        log!(self.log_level, "{}", formatted_log);
    }
}

#[cfg(test)]
mod tests {
    use log::{debug, Level};
    use plonky2::{
        field::types::Field,
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };

    use crate::{
        profiling_enable,
        types::bytes::{CircuitBuilderBytes, WitnessBytes},
        watchers::target_watcher::TargetWatcher,
    };

    #[test]
    fn test_watcher() {
        profiling_enable();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        // The arithmetic circuit.
        let initial = builder.add_virtual_target();
        let mut cur_target = initial;
        for i in 2..10 {
            let i_target = builder.constant(F::from_canonical_u32(i));
            cur_target = builder.mul(cur_target, i_target);
            builder.watch(&cur_target, "intermediate result");
        }

        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_input(initial);
        builder.register_public_input(cur_target);

        let mut pw = PartialWitness::new();
        pw.set_target(initial, F::ONE);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        println!(
            "Factorial starting at {} is {}",
            proof.public_inputs[0], proof.public_inputs[1]
        );

        data.verify(proof);
    }
}
