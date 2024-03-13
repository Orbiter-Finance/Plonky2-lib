pub mod utils;

use crate::nonnative::biguint::ReadBigUintTarget;
use crate::storage::gadgets::utils::get_map_storage_location;
use crate::types::bytes::{
    AddressTarget, Bytes32Target, CircuitBuilderBytes, GeneratedValuesBytes, U256Target,
    WitnessBytes,
};
use crate::types::serialization::ReadBytes;
use ethers_core::types::H256;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::Target;
use plonky2::iop::witness::PartitionWitness;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{Buffer, IoResult, Read, Write};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use plonky2_u32::serialization::ReadU32;
use plonky2_u32::witness::WitnessU32;
use std::marker::PhantomData;

#[derive(Debug, Clone, Default)]
pub struct EthStorageKeyGenerator<F: RichField + Extendable<D>, const D: usize> {
    mapping_location: U32Target,
    map_key: Bytes32Target,
    pub value: Bytes32Target,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> EthStorageKeyGenerator<F, D> {
    pub fn new(
        builder: &mut CircuitBuilder<F, D>,
        mapping_location: U32Target,
        map_key: Bytes32Target,
    ) -> EthStorageKeyGenerator<F, D> {
        let value = builder.add_virtual_bytes32_target();
        EthStorageKeyGenerator {
            mapping_location,
            map_key,
            value,
            _phantom: PhantomData,
        }
    }

    pub fn id() -> String {
        "EthStorageKeyGenerator".to_string()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for EthStorageKeyGenerator<F, D>
{
    fn id(&self) -> String {
        Self::id()
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut targets = Vec::new();
        targets.push(self.mapping_location.0);
        targets.extend(self.map_key.targets());
        targets
    }

    fn run_once(&self, witness: &PartitionWitness<F>, buffer: &mut GeneratedValues<F>) {
        let (mapping_location, _) = witness.get_u32_target(self.mapping_location);
        let map_key = witness.get_bytes32_target(self.map_key);
        let map_key = H256::from_slice(map_key.as_slice());

        let location = get_map_storage_location(mapping_location as u128, map_key);
        buffer.set_bytes32_target(&self.value, location.as_bytes().to_vec());
    }

    #[allow(unused_variables)]
    fn serialize(&self, dst: &mut Vec<u8>, common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target(self.mapping_location.0)?;
        dst.write_target_vec(&self.map_key.targets())?;
        dst.write_target_vec(&self.value.targets())
    }

    #[allow(unused_variables)]
    fn deserialize(src: &mut Buffer, common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let mapping_location = src.read_target_u32()?;
        let map_key = src.read_byte32_target()?;
        let value = src.read_byte32_target()?;
        Ok(Self {
            mapping_location,
            map_key,
            value,
            _phantom: PhantomData,
        })
    }
}
