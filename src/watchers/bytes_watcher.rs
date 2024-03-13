use log::log;
use std::marker::PhantomData;

use log::Level;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness},
    },
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CommonCircuitData},
    util::serialization::IoResult,
};

use crate::types::bytes::ByteTarget;

pub trait BytesWatcher<F: RichField + Extendable<D>, const D: usize> {
    fn watch_byte(&mut self, target: &ByteTarget, log: &str);

    fn watch_bytes(&mut self, targets: &[ByteTarget], log: &str);
}

impl<F: RichField + Extendable<D>, const D: usize> BytesWatcher<F, D> for CircuitBuilder<F, D> {
    fn watch_byte(&mut self, byte_target: &ByteTarget, log: &str) {
        let targets = vec![byte_target.clone()];
        let log = String::from(log);
        let generator = BytesWatchGenerator {
            targets,
            log,
            log_level: Level::Info,
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);
    }
    fn watch_bytes(&mut self, targets: &[ByteTarget], log: &str) {
        let targets = targets.to_vec();
        let log = String::from(log);
        let generator = BytesWatchGenerator {
            targets,
            log,
            log_level: Level::Info,
            _phantom: PhantomData,
        };
        self.add_simple_generator(generator);
    }
}

#[derive(Debug, Clone)]

pub struct BytesWatchGenerator<F: RichField, const D: usize> {
    pub targets: Vec<ByteTarget>,
    pub log: String,
    pub log_level: Level,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> BytesWatchGenerator<F, D> {
    pub fn id() -> String {
        "BytesWatchGenerator".to_string()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for BytesWatchGenerator<F, D>
{
    fn id(&self) -> String {
        Self::id()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.targets
            .iter()
            .flat_map(|t| t.elements_targets())
            .collect()
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        todo!()
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, _out_buffer: &mut GeneratedValues<F>) {
        let bytes: Vec<u8> = self
            .targets
            .iter()
            .map(|byte_target| byte_target_to_u8(byte_target, witness))
            .collect();

        let hex_str = bytes_to_hex_str(&bytes);

        let formatted_log = format!("[Watch] {}: {}", self.log, hex_str);
        log!(self.log_level, "{}", formatted_log);
    }
}

fn byte_target_to_u8<F: RichField>(byte_target: &ByteTarget, witness: &PartitionWitness<F>) -> u8 {
    byte_target
        .as_le_bits()
        .iter()
        .enumerate()
        .fold(0, |acc, (i, bool_target)| {
            let bit_value = witness.get_bool_target(*bool_target);
            if bit_value {
                acc | (1 << i)
            } else {
                acc
            }
        })
}

fn bytes_to_hex_str(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|byte| format!("{:02X}", byte))
        .collect::<Vec<String>>()
        .join("")
}

#[cfg(test)]
mod tests {
    use log::{debug, Level};
    use plonky2::{
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };

    use crate::{
        profiling_enable,
        types::bytes::{CircuitBuilderBytes, WitnessBytes},
        watchers::bytes_watcher::BytesWatcher,
    };

    #[test]
    fn test_watcher() {
        profiling_enable();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let test_bytes: crate::types::bytes::BytesTarget<4> = builder.add_virtual_bytes_target();
        let test_bytes_slice = test_bytes.as_slice();
        builder.watch_bytes(test_bytes_slice, "test bytes");

        let mut pw = PartialWitness::new();
        pw.set_bytes_target(&test_bytes, vec![255, 15, 2, 1]);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof);
    }
}
