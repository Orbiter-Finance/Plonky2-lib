use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;
use plonky2::field::types::Sample;
use plonky2::hash::hash_types::HashOut;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use crate::recursive_proof::config::PoseidonBN128GoldilocksConfig;
use crate::recursive_proof::recursive_verifier::{generate_circom_verifier, generate_proof_base64, generate_verifier_config, recursive_proof};
use crate::zkdsa::gadgets::signature::SimpleSignatureTarget;
use anyhow::Result;

#[test]
fn ecdsa_sig_test() -> Result<()> {
    const D: usize = 2; // extension degree
    type C = PoseidonGoldilocksConfig;
    type H = <C as GenericConfig<D>>::InnerHasher;
    type F = <C as GenericConfig<D>>::F;
    // type F = GoldilocksField;

    let standard_config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(standard_config.clone());

    let target = SimpleSignatureTarget::add_virtual_to::<F, H, D>(&mut builder);
    builder.register_public_inputs(&target.message.elements);
    builder.register_public_inputs(&target.public_key.elements);
    builder.register_public_inputs(&target.signature.elements);
    let data = builder.build::<C>();

    let private_key = HashOut::<F>::rand();
    let message = HashOut::<F>::rand();

    let mut pw = PartialWitness::new();
    target.set_witness(&mut pw, private_key, message);

    println!("start proving");
    let start = Instant::now();
    let proof = data.prove(pw).unwrap();
    let end = start.elapsed();
    println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

    // dbg!(&proof.public_inputs);

    match data.verify(proof.clone()) {
        Ok(()) => println!("Ok!"),
        Err(x) => println!("{}", x),
    }

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