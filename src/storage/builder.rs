use crate::mpt::utils::public_inputs_to_hex;
use crate::nonnative::biguint::BigUintTarget;
use crate::storage::gadgets::utils::get_map_storage_location;
use crate::storage::gadgets::EthStorageKeyGenerator;
use crate::storage::types::{StorageKeyInput, StorageKeyInputTarget};
use crate::storage::witness::WitnessStorage;
use crate::types::bytes::{Bytes32Target, CircuitBuilderBytes, U256Target};
use core::str::FromStr;
use ethers::prelude::U256;
use ethers_core::types::H256;
use log::debug;
use plonky2::field::extension::Extendable;
use plonky2::field::types::PrimeField64;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, Witness};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, KeccakGoldilocksConfig};
use plonky2_u32::gadgets::arithmetic_u32::CircuitBuilderU32;

pub trait CircuitBuilderStorage<F: RichField + Extendable<D>, const D: usize> {
    fn add_virtual_storage_key_input_target(&mut self) -> StorageKeyInputTarget;
    fn get_storage_key(&mut self, target: &StorageKeyInputTarget) -> Bytes32Target;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderStorage<F, D>
    for CircuitBuilder<F, D>
{
    fn add_virtual_storage_key_input_target(&mut self) -> StorageKeyInputTarget {
        let mapping_location = self.add_virtual_u32_target();
        let map_key = self.add_virtual_bytes32_target();
        StorageKeyInputTarget {
            mapping_location,
            map_key,
        }
    }

    fn get_storage_key(&mut self, target: &StorageKeyInputTarget) -> Bytes32Target {
        let generator = EthStorageKeyGenerator::new(self, target.mapping_location, target.map_key);
        let value = generator.value;
        self.add_simple_generator(generator);
        value
    }
}

#[test]
fn test_get_storage_key_at() {
    const D: usize = 2;
    type C = KeccakGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    let config = CircuitConfig::standard_recursion_config();

    let mut builder = CircuitBuilder::<F, D>::new(config);

    let input_target = builder.add_virtual_storage_key_input_target();

    let value = builder.get_storage_key(&input_target);
    builder.register_public_inputs(value.targets().as_slice());

    // Build your circuit.
    let data = builder.build::<C>();

    // Write to the circuit input.
    let mut pw = PartialWitness::new();
    {
        let input = StorageKeyInput {
            mapping_location: 0,
            map_key: H256::from_str(
                "0x281dc31bb78779a1ede7bf0f4d2bc5f07ddebc9f9d1155e413d8804384604bbe",
            )
            .unwrap(),
        };

        pw.set_storage_key_input_target(&input_target, &input);

        println!(
            "storage key: {:?}",
            get_map_storage_location(input.mapping_location as u128, input.map_key)
        );
    }

    let proof = data.prove(pw).unwrap();
    println!("public inputs {:?}", proof.public_inputs);
    public_inputs_to_hex::<F, D>(proof.public_inputs.clone());
    assert!(data.verify(proof).is_ok());
    // assert_eq!(
    //     circuit_value,
    //     bytes32!("0xca77d4e79102603cb6842afffd8846a3123877159ed214aeadfc4333d595fd50"),
    // );
    //
    // // initialize serializers
    // let gate_serializer = GateRegistry::<L, D>::new();
    // let hint_serializer = HintRegistry::<L, D>::new();
    //
    // // test serialization
    // let _ = circuit
    //     .serialize(&gate_serializer, &hint_serializer)
    //     .unwrap();
}
