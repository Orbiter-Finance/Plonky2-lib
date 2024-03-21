use crate::hash::keccak256::{CircuitBuilderHashKeccak, WitnessHashKeccak, KECCAK256_R};
use crate::hash::CircuitBuilderHash;
use crate::recursive_proof::config::PoseidonBN128GoldilocksConfig;
use crate::recursive_proof::recursive_verifier::{
    generate_circom_verifier, generate_proof_base64, generate_verifier_config, recursive_proof,
};
use anyhow::Result;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use sha3::{Digest, Keccak256};
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
#[test]
fn keccak_test() -> Result<()> {
    let input_test = [
        // short hash, e.g. last step of storage proof
        "e19f37a9fe364faab93b216da50a3214154f22a0a2b415b23a84c8169e8b636ee301",
        "19225e4ee19eb5a11e5260392e6d5154d4bc6a35d89c9d18bf6a63104e9bbcc2",
    ];

    // build circuit once
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let standard_config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(standard_config.clone());
    let hash_target = builder.add_virtual_hash_input_target(1, KECCAK256_R);
    let hash_output = builder.hash_keccak256(&hash_target);
    builder.public_hash_output(&hash_output);
    let num_gates = builder.num_gates();
    // let copy_constraints = builder.copy_constraints.len();
    let copy_constraints = "<private>";
    let data = builder.build::<C>();
    println!(
        "keccak256 num_gates={}, copy_constraints={}, quotient_degree_factor={}",
        num_gates, copy_constraints, data.common.quotient_degree_factor
    );

    let input = hex::decode(input_test[0]).unwrap();
    let output = hex::decode(input_test[1]).unwrap();

    // test program
    let mut hasher = Keccak256::new();
    hasher.update(input.as_slice());
    let result = hasher.finalize();
    assert_eq!(result[..], output[..]);

    // test circuit
    let mut pw = PartialWitness::new();
    pw.set_keccak256_input_target(&hash_target, &input);
    pw.set_keccak256_output_target(&hash_output, &output);

    let proof = data.prove(pw).unwrap();
    assert!(data.verify(proof.clone()).is_ok());

    let (proof, vd, cd) = recursive_proof::<F, C, C, D>(
        proof,
        data.verifier_only,
        data.common,
        &standard_config,
        None,
        true,
        true,
    )?;

    type CBn128 = PoseidonBN128GoldilocksConfig;
    let (proof, vd, cd) =
        recursive_proof::<F, CBn128, C, D>(proof, vd, cd, &standard_config, None, true, true)?;

    let conf = generate_verifier_config(&proof, &vd)?;
    let (circom_constants, circom_gates) = generate_circom_verifier(&conf, &cd, &vd)?;

    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("src/recursive_proof/circuits/constants.circom");
    let mut circom_file = File::create(path)?;
    circom_file.write_all(circom_constants.as_bytes())?;

    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("src/recursive_proof/circuits/gates.circom");
    circom_file = File::create(path)?;
    circom_file.write_all(circom_gates.as_bytes())?;

    let proof_json = generate_proof_base64(&proof, &conf, &vd)?;

    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("src/recursive_proof/test_data");
    if !Path::new(&path).is_dir() {
        std::fs::create_dir(path)?;
    }

    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("src/recursive_proof/test_data/proof.json");
    let mut proof_file = File::create(path)?;
    proof_file.write_all(proof_json.as_bytes())?;

    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("src/recursive_proof/test_data/conf.json");
    let mut conf_file = File::create(path)?;
    conf_file.write_all(serde_json::to_string(&conf)?.as_ref())?;

    Ok(())
}
