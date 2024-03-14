use std::marker::PhantomData;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness},
    },
    plonk::circuit_data::CommonCircuitData,
    util::serialization::{Buffer, IoResult},
};
use plonky2_u32::{
    gadgets::arithmetic_u32::U32Target,
    witness::{GeneratedValuesU32, WitnessU32},
};
use serde::{Deserialize, Serialize};

use crate::{
    types::bytes::{ByteTarget, BytesTarget, GeneratedValuesBytes, WitnessBytes},
    watchers::bytes_watcher::byte_target_to_u8,
};

use super::{
    builder::{MPTNodeTarget, MAX_MPT_NODE_SIZE},
    utils::decode_padded_mpt_node,
};

#[derive(Debug, Clone)]
pub struct DecodeRLPNodeGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub encoded: Vec<ByteTarget>,
    pub len: U32Target,
    pub skip_computation: BoolTarget,
    pub decoded_mpt_node: MPTNodeTarget,
    pub(crate) _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for DecodeRLPNodeGenerator<F, D>
{
    fn id(&self) -> String {
        "DecodeRLPNodeGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut deps = Vec::new();

        // Flatten and extend `deps` with `encoded` dependencies directly
        self.encoded
            .iter()
            .flat_map(|encoded_target| encoded_target.elements_targets())
            .for_each(|dep| deps.push(dep));

        // Directly add `len` and `skip_computation` dependencies
        deps.push(self.len.0);
        deps.push(self.skip_computation.target);

        deps
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        // prase the dynamic circuit target values
        let encoded_bytes: Vec<u8> = self
            .encoded
            .iter()
            .map(|byte_target| byte_target_to_u8(byte_target, witness))
            .collect();
        let encoded_bytes_len = witness
            .try_get_target(self.len.0)
            .unwrap()
            .to_canonical_u64();
        let skip_computation = witness.get_bool_target(self.skip_computation);

        // calculation outside of the circuit
        let mpt_node_fixed_size = decode_padded_mpt_node(
            &encoded_bytes,
            encoded_bytes_len.try_into().unwrap(),
            skip_computation,
        );

        // set the MPTNodeTarget
        // set the `data` field
        let data_for_target: Vec<Vec<u8>> = mpt_node_fixed_size
            .data
            .iter()
            .map(|item| item.data.iter().map(|&byte| byte as u8).collect())
            .collect();

        for (u, t) in data_for_target
            .iter()
            .zip(self.decoded_mpt_node.data.as_slice().iter())
        {
            out_buffer.set_bytes32_target(t, u.clone());
        }

        // Set the `lens` field
        let lens_as_u32: Vec<u32> = mpt_node_fixed_size
            .data
            .iter()
            .map(|item| item.len as u32)
            .collect();
        for (u, t) in lens_as_u32
            .iter()
            .zip(self.decoded_mpt_node.lens.0)
            .into_iter()
        {
            out_buffer.set_u32_target(t, u.clone());
        }

        // Set the `len` field
        out_buffer.set_u32_target(self.decoded_mpt_node.len, mpt_node_fixed_size.len as u32);
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        todo!()
    }

    fn deserialize(source: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        todo!()
    }
}
