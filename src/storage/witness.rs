use crate::storage::types::{StorageKeyInput, StorageKeyInputTarget};
use crate::types::bytes::WitnessBytes;
use plonky2::field::types::PrimeField64;
use plonky2::iop::witness::Witness;
use plonky2_u32::witness::WitnessU32;

pub trait WitnessStorage<F: PrimeField64>: Witness<F> {
    fn set_storage_key_input_target(
        &mut self,
        target: &StorageKeyInputTarget,
        input: &StorageKeyInput,
    );
}

impl<T: Witness<F>, F: PrimeField64> WitnessStorage<F> for T {
    fn set_storage_key_input_target(
        &mut self,
        target: &StorageKeyInputTarget,
        input: &StorageKeyInput,
    ) {
        let map_key = input.map_key.as_bytes().iter().map(|&v| v as u32).collect();
        self.set_bytes32_target(&target.map_key, map_key);

        self.set_u32_target(target.mapping_location, input.mapping_location);
    }
}
