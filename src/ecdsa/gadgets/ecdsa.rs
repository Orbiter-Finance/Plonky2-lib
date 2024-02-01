use core::marker::PhantomData;
use std::fs::File;
use std::io::Write;

use plonky2::field::extension::Extendable;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::secp256k1_base::Secp256K1Base;
use plonky2::field::secp256k1_scalar::Secp256K1Scalar;
use plonky2::field::types::{PrimeField, Sample};
use plonky2::gadgets::arithmetic::EqualityGenerator;
use plonky2::gadgets::split_base::BaseSumGenerator;
use plonky2::gates::arithmetic_base::{ArithmeticBaseGenerator, ArithmeticGate};
use plonky2::gates::arithmetic_extension::ArithmeticExtensionGate;
use plonky2::gates::base_sum::{BaseSplitGenerator, BaseSumGate};
use plonky2::gates::constant::ConstantGate;
use plonky2::gates::coset_interpolation::CosetInterpolationGate;
use plonky2::gates::exponentiation::ExponentiationGate;
use plonky2::gates::lookup::LookupGate;
use plonky2::gates::lookup_table::LookupTableGate;
use plonky2::gates::multiplication_extension::MulExtensionGate;
use plonky2::gates::noop::NoopGate;
use plonky2::gates::poseidon::{PoseidonGate, PoseidonGenerator};
//use plonky2::gates::poseidon2::{Poseidon2Gate, Poseidon2Generator};
use plonky2::gates::poseidon_mds::{PoseidonMdsGate, PoseidonMdsGenerator};
use plonky2::gates::public_input::PublicInputGate;
use plonky2::gates::random_access::{RandomAccessGate, RandomAccessGenerator};
use plonky2::gates::reducing::ReducingGate;
use plonky2::gates::reducing_extension::ReducingExtensionGate;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{
    generate_partial_witness_cuda, ConstantGenerator, RandomValueGenerator,
};
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitDataOneDim;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::{
    AlgebraicHasher, GenericConfig, Poseidon2GoldilocksConfig, PoseidonGoldilocksConfig,
};
use plonky2::recursion::dummy_circuit::DummyProofGenerator;
use plonky2::util::serialization::{GateSerializer, WitnessGeneratorSerializer};
use plonky2_u32::gates::add_many_u32::{U32AddManyGate, U32AddManyGenerator};
use plonky2_u32::gates::arithmetic_u32::{U32ArithmeticGate, U32ArithmeticGenerator};
use plonky2_u32::gates::comparison::{ComparisonGate, ComparisonGenerator};
use plonky2_u32::gates::range_check_u32::{U32RangeCheckGate, U32RangeCheckGenerator};
use plonky2_u32::gates::subtraction_u32::{U32SubtractionGate, U32SubtractionGenerator};

use crate::ecdsa::curve::curve_types::{Curve, CurveScalar};
use crate::ecdsa::curve::ecdsa::{sign_message, ECDSAPublicKey, ECDSASecretKey, ECDSASignature};
use crate::ecdsa::curve::secp256k1::Secp256K1;
use crate::ecdsa::gadgets::biguint::WitnessBigUint;
use crate::ecdsa::gadgets::curve::{AffinePointTarget, CircuitBuilderCurve};
use crate::ecdsa::gadgets::curve_fixed_base::{
    fixed_base_curve_mul_circuit, fixed_base_curve_mul_circuit_without_return,
};
use crate::ecdsa::gadgets::glv::CircuitBuilderGlv;
use crate::ecdsa::gadgets::nonnative::{
    CircuitBuilderNonNative, NonNativeScalarAdditionGenerator, NonNativeScalarInverseGenerator,
    NonNativeScalarMultiplicationGenerator, NonNativeScalarSubtractionGenerator, NonNativeTarget,
};
use crate::profiling_enable;
use plonky2::{
    get_gate_tag_impl, get_generator_tag_impl, impl_gate_serializer, impl_generator_serializer,
    read_gate_impl, read_generator_impl,
};

use super::glv::GLVDecompositionGenerator;
use super::nonnative::{
    NonNativeAdditionGenerator, NonNativeInverseGenerator, NonNativeMultiplicationGenerator,
    NonNativeSubtractionGenerator,
};

use ethers_core::utils::keccak256;
#[derive(Clone, Debug)]
pub struct ECDSASecretKeyTarget<C: Curve>(pub NonNativeTarget<C::ScalarField>);

#[derive(Clone, Debug)]
pub struct ECDSAPublicKeyTarget<C: Curve>(pub AffinePointTarget<C>);

#[derive(Clone, Debug)]
pub struct ECDSASignatureTarget<C: Curve> {
    pub r: NonNativeTarget<C::ScalarField>,
    pub s: NonNativeTarget<C::ScalarField>,
}

const ECDSA_BATCH_SIZE: usize = 20;
const PROVE_RUN_TIMES: usize = 3;

pub struct CustomGateSerializer;

impl<F: RichField + Extendable<D>, const D: usize> GateSerializer<F, D> for CustomGateSerializer {
    impl_gate_serializer! {
        DefaultGateSerializer,
        ArithmeticGate,
        ArithmeticExtensionGate<D>,
        BaseSumGate<4>,
        ConstantGate,
        CosetInterpolationGate<F, D>,
        ComparisonGate<F, D>,
        ExponentiationGate<F, D>,
        LookupGate,
        LookupTableGate,
        MulExtensionGate<D>,
        NoopGate,
        PoseidonMdsGate<F, D>,
        PoseidonGate<F, D>,
        //Poseidon2Gate<F, D>,
        PublicInputGate,
        RandomAccessGate<F, D>,
        ReducingExtensionGate<D>,
        ReducingGate<D>,
        U32AddManyGate<F, D>,
        U32ArithmeticGate<F, D>,
        U32RangeCheckGate<F, D>,
        U32SubtractionGate<F, D>
    }
}

pub struct CustomGeneratorSerializer<
    C: GenericConfig<D>,
    FF1: PrimeField,
    FF2: PrimeField,
    const D: usize,
> {
    pub _phantom: PhantomData<C>,
    pub _phantom2: PhantomData<FF1>,
    pub _phantom3: PhantomData<FF2>,
}

impl<F, FF1, FF2, C, const D: usize> WitnessGeneratorSerializer<F, D>
    for CustomGeneratorSerializer<C, FF1, FF2, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
    FF1: PrimeField,
    FF2: PrimeField,
{
    impl_generator_serializer! {
        // CustomGeneratorSerializer,
        DummyProofGenerator<F, C, D>,
        ArithmeticBaseGenerator<F, D>,
        ConstantGenerator<F>,
        PoseidonGenerator<F, D>,
        PoseidonMdsGenerator<D>,
        //Poseidon2Generator<F, D>,
        RandomValueGenerator,
        BaseSumGenerator<4>,
        NonNativeMultiplicationGenerator<F, D, FF1>,
        NonNativeScalarMultiplicationGenerator<F, D>,
        NonNativeAdditionGenerator<F, D, FF1>,
        NonNativeScalarAdditionGenerator<F, D>,
        NonNativeInverseGenerator<F, D, FF1>,
        NonNativeScalarInverseGenerator<F, D>,
        NonNativeSubtractionGenerator<F, D, FF1>,
        NonNativeScalarSubtractionGenerator<F, D>,
        GLVDecompositionGenerator<F, D>,
        U32RangeCheckGenerator<F, D>,
        EqualityGenerator,
        U32ArithmeticGenerator<F, D>,
        U32AddManyGenerator<F, D>,
        ComparisonGenerator<F,D>,
        BaseSplitGenerator<4>,
        RandomAccessGenerator<F, D>,
        U32SubtractionGenerator<F, D>
    }
}

pub fn verify_message_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    msg: NonNativeTarget<Secp256K1Scalar>,
    sig: ECDSASignatureTarget<Secp256K1>,
    pk: ECDSAPublicKeyTarget<Secp256K1>,
) {
    let ECDSASignatureTarget { r, s } = sig;

    builder.curve_assert_valid(&pk.0);

    let c = builder.inv_nonnative(&s);
    let u1 = builder.mul_nonnative(&msg, &c);
    let u2 = builder.mul_nonnative(&r, &c);

    let point1 = fixed_base_curve_mul_circuit(builder, Secp256K1::GENERATOR_AFFINE, &u1);
    let point2 = builder.glv_mul(&pk.0, &u2);
    let point = builder.curve_add(&point1, &point2);

    let x = NonNativeTarget::<Secp256K1Scalar> {
        value: point.x.value,
        _phantom: PhantomData,
    };
    builder.connect_nonnative(&r, &x);
}

pub fn batch_verify_message_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    msgs: Vec<NonNativeTarget<Secp256K1Scalar>>,
    sigs: Vec<ECDSASignatureTarget<Secp256K1>>,
    pks: Vec<ECDSAPublicKeyTarget<Secp256K1>>,
) {
    assert_eq!(msgs.len(), sigs.len());
    assert_eq!(msgs.len(), pks.len());

    for ((msg, sig), pk) in msgs.into_iter().zip(sigs.into_iter()).zip(pks.into_iter()) {
        let ECDSASignatureTarget { r, s } = sig;

        builder.curve_assert_valid(&pk.0);

        let c = builder.inv_nonnative_scalar(&s);
        let u1 = builder.mul_nonnative_scalar(&msg, &c);
        let u2 = builder.mul_nonnative_scalar(&r, &c);

        let point1 = fixed_base_curve_mul_circuit(builder, Secp256K1::GENERATOR_AFFINE, &u1);
        let point2 = builder.glv_mul_scalar(&pk.0, &u2);
        let point = builder.curve_add(&point1, &point2);

        let x = NonNativeTarget::<Secp256K1Scalar> {
            value: point.x.value,
            _phantom: PhantomData,
        };
        builder.connect_nonnative(&r, &x);
    }
}

/// Generate a batch of ECDSA data
pub fn gen_batch_ecdsa_data(
    batch_num: usize,
) -> (
    Vec<Secp256K1Scalar>,
    Vec<ECDSASignature<Secp256K1>>,
    Vec<ECDSAPublicKey<Secp256K1>>,
) {
    type Curve = Secp256K1;
    let mut msgs = Vec::with_capacity(batch_num);
    let mut sigs = Vec::with_capacity(batch_num);
    let mut pks = Vec::with_capacity(batch_num);
    for i in 0..batch_num {
        let msg = Secp256K1Scalar::rand();
        let sk = ECDSASecretKey::<Curve>(Secp256K1Scalar::rand());
        let pk = ECDSAPublicKey((CurveScalar(sk.0) * Curve::GENERATOR_PROJECTIVE).to_affine());
        let sig = sign_message(msg, sk);
        let ECDSASignature { r, s } = sig;
        msgs.push(msg);
        pks.push(pk);
        sigs.push(sig);
    }

    (msgs, sigs, pks)
}

pub fn test_batch_ecdsa_circuit_with_config(batch_num: usize, config: CircuitConfig) {
    profiling_enable();
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    println!(
        "BATCH SIZE {} GenericConfig {}",
        batch_num,
        C::config_type()
    );

    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut v_msg_target = Vec::with_capacity(batch_num);
    let mut v_msg_biguint_target = Vec::with_capacity(batch_num);
    let mut v_pk_target = Vec::with_capacity(batch_num);
    let mut v_pk_x_biguint_target = Vec::with_capacity(batch_num);
    let mut v_pk_y_biguint_target = Vec::with_capacity(batch_num);
    let mut v_r_biguint_target = Vec::with_capacity(batch_num);
    let mut v_s_biguint_target = Vec::with_capacity(batch_num);
    let mut v_sig_target = Vec::with_capacity(batch_num);

    for _i in 0..batch_num {
        let msg_target: NonNativeTarget<Secp256K1Scalar> = builder.add_virtual_nonnative_target();
        let msg_biguint_target = builder.nonnative_to_canonical_biguint(&msg_target);

        // let pk_target = ECDSAPublicKeyTarget(builder.constant_affine_point(pk.0));
        // TODO: builder.constant_affine_point(pk.0) has an extra debug_assert!(!point.zero);
        let pk_target: ECDSAPublicKeyTarget<Secp256K1> =
            ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target());
        let pk_x_biguint_target = builder.nonnative_to_canonical_biguint(&pk_target.0.x);
        let pk_y_biguint_target = builder.nonnative_to_canonical_biguint(&pk_target.0.y);

        let r_target: NonNativeTarget<Secp256K1Scalar> = builder.add_virtual_nonnative_target();
        let r_biguint_target = builder.nonnative_to_canonical_biguint(&r_target);

        let s_target: NonNativeTarget<_> = builder.add_virtual_nonnative_target();
        let s_biguint_target = builder.nonnative_to_canonical_biguint(&s_target);

        let sig_target: ECDSASignatureTarget<Secp256K1> = ECDSASignatureTarget {
            r: r_target,
            s: s_target,
        };
        v_msg_target.push(msg_target);
        v_msg_biguint_target.push(msg_biguint_target);
        v_pk_target.push(pk_target);
        v_pk_x_biguint_target.push(pk_x_biguint_target);
        v_pk_y_biguint_target.push(pk_y_biguint_target);
        v_r_biguint_target.push(r_biguint_target);
        v_s_biguint_target.push(s_biguint_target);
        v_sig_target.push(sig_target);
    }

    batch_verify_message_circuit(&mut builder, v_msg_target, v_sig_target, v_pk_target);

    dbg!(builder.num_gates());

    let gate_serializer = CustomGateSerializer;

    let generator_serializer = CustomGeneratorSerializer {
        _phantom: PhantomData::<C>,
        _phantom2: PhantomData::<Secp256K1Base>,
        _phantom3: PhantomData::<Secp256K1Scalar>,
    };

    let path_string = "data/data_".to_string() + &batch_num.to_string() + "_bytes";
    let path = std::path::Path::new(&path_string);
    let data = if path.exists() {
        println!("Reading data");
        let circuit_data_bytes = std::fs::read(path).unwrap();
        let circuit_data = CircuitData::<F, C, D>::from_bytes(
            &circuit_data_bytes,
            &gate_serializer,
            &generator_serializer,
        )
        .unwrap();
        circuit_data
    } else {
        let data = builder.build::<C>();
        let data_bytes = data
            .to_bytes(&gate_serializer, &generator_serializer)
            .map_err(|_| anyhow::Error::msg("CircuitData serialization failed."))
            .unwrap();
        println!("Writing data");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let mut file = File::create(path).unwrap();
        file.write_all(&data_bytes).unwrap();
        data
    };

    for j in 0..PROVE_RUN_TIMES {
        let j = std::hint::black_box(j);
        let (msg_list, sig_list, pk_list) = gen_batch_ecdsa_data(batch_num);
        let mut pw = PartialWitness::new();
        for i in 0..batch_num {
            let ECDSASignature { r, s } = sig_list[i];

            let msg_biguint = msg_list[i].to_canonical_biguint();
            let pk_x_biguint = pk_list[i].0.x.to_canonical_biguint();
            let pk_y_biguint = pk_list[i].0.y.to_canonical_biguint();
            let r_biguint = r.to_canonical_biguint();
            let s_biguint = s.to_canonical_biguint();

            pw.set_biguint_target(&v_msg_biguint_target[i], &msg_biguint);
            pw.set_biguint_target(&v_r_biguint_target[i], &r_biguint);
            pw.set_biguint_target(&v_s_biguint_target[i], &s_biguint);
            pw.set_biguint_target(&v_pk_x_biguint_target[i], &pk_x_biguint);
            pw.set_biguint_target(&v_pk_y_biguint_target[i], &pk_y_biguint);
        }
        //let pw = pw.clone();
        let proof = std::hint::black_box(data.prove(pw).unwrap());

        println!("proof PIS {:?}", proof.public_inputs);
        data.verify(proof).unwrap();
        println!("-------------------------{j}th prove finished!-------------------------------");
        //println!("sleeping 600s...");
        //std::thread::sleep(std::time::Duration::from_secs(600));
        //println!("sleeping 600s finished");
    }

    // let proof = data.prove(pw).unwrap();

    // println!("proof PIS {:?}", proof.public_inputs);
    // data.verify(proof).unwrap();
}

pub fn test_batch_ecdsa_cuda_circuit_with_config(batch_num: usize, config: CircuitConfig) {
    profiling_enable();
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    println!(
        "BATCH SIZE {} GenericConfig {}",
        batch_num,
        C::config_type()
    );

    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut v_msg_target = Vec::with_capacity(batch_num);
    let mut v_msg_biguint_target = Vec::with_capacity(batch_num);
    let mut v_pk_target = Vec::with_capacity(batch_num);
    let mut v_pk_x_biguint_target = Vec::with_capacity(batch_num);
    let mut v_pk_y_biguint_target = Vec::with_capacity(batch_num);
    let mut v_r_biguint_target = Vec::with_capacity(batch_num);
    let mut v_s_biguint_target = Vec::with_capacity(batch_num);
    let mut v_sig_target = Vec::with_capacity(batch_num);

    for _i in 0..batch_num {
        let msg_target: NonNativeTarget<Secp256K1Scalar> = builder.add_virtual_nonnative_target();
        let msg_biguint_target = builder.nonnative_to_canonical_biguint(&msg_target);

        // let pk_target = ECDSAPublicKeyTarget(builder.constant_affine_point(pk.0));
        // TODO: builder.constant_affine_point(pk.0) has an extra debug_assert!(!point.zero);
        let pk_target: ECDSAPublicKeyTarget<Secp256K1> =
            ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target());
        let pk_x_biguint_target = builder.nonnative_to_canonical_biguint(&pk_target.0.x);
        let pk_y_biguint_target = builder.nonnative_to_canonical_biguint(&pk_target.0.y);

        let r_target: NonNativeTarget<Secp256K1Scalar> = builder.add_virtual_nonnative_target();
        let r_biguint_target = builder.nonnative_to_canonical_biguint(&r_target);

        let s_target: NonNativeTarget<_> = builder.add_virtual_nonnative_target();
        let s_biguint_target = builder.nonnative_to_canonical_biguint(&s_target);

        let sig_target: ECDSASignatureTarget<Secp256K1> = ECDSASignatureTarget {
            r: r_target,
            s: s_target,
        };
        v_msg_target.push(msg_target);
        v_msg_biguint_target.push(msg_biguint_target);
        v_pk_target.push(pk_target);
        v_pk_x_biguint_target.push(pk_x_biguint_target);
        v_pk_y_biguint_target.push(pk_y_biguint_target);
        v_r_biguint_target.push(r_biguint_target);
        v_s_biguint_target.push(s_biguint_target);
        v_sig_target.push(sig_target);
    }

    batch_verify_message_circuit(&mut builder, v_msg_target, v_sig_target, v_pk_target);

    dbg!(builder.num_gates());

    // let data = builder.build_cuda::<C>();
    let gate_serializer = CustomGateSerializer;

    let generator_serializer = CustomGeneratorSerializer {
        _phantom: PhantomData::<C>,
        _phantom2: PhantomData::<Secp256K1Base>,
        _phantom3: PhantomData::<Secp256K1Scalar>,
    };

    let path_string = "data/data_cuda_".to_string() + &batch_num.to_string() + "_bytes";
    let path = std::path::Path::new(&path_string);
    let data = if path.exists() {
        let start_timer = std::time::Instant::now();
        println!("Reading data");
        let circuit_data_bytes = std::fs::read(path).unwrap();
        let circuit_data = CircuitDataOneDim::<F, C, D>::from_bytes(
            &circuit_data_bytes,
            &gate_serializer,
            &generator_serializer,
        )
        .unwrap();
        println!("Reading data need time: {:?}", start_timer.elapsed());
        circuit_data
    } else {
        let data = builder.build_cuda::<C>();
        let data_bytes = data
            .to_bytes(&gate_serializer, &generator_serializer)
            .map_err(|_| anyhow::Error::msg("CircuitData serialization failed."))
            .unwrap();
        println!("Writing data");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let mut file = File::create(path).unwrap();
        file.write_all(&data_bytes).unwrap();
        data
    };

    for j in 0..PROVE_RUN_TIMES {
        //let j = std::hint::black_box(j);
        let (msg_list, sig_list, pk_list) = gen_batch_ecdsa_data(batch_num);

        let mut pw = PartialWitness::new();
        for i in 0..batch_num {
            let ECDSASignature { r, s } = sig_list[i];

            let msg_biguint = msg_list[i].to_canonical_biguint();
            let pk_x_biguint = pk_list[i].0.x.to_canonical_biguint();
            let pk_y_biguint = pk_list[i].0.y.to_canonical_biguint();
            let r_biguint = r.to_canonical_biguint();
            let s_biguint = s.to_canonical_biguint();

            pw.set_biguint_target(&v_msg_biguint_target[i], &msg_biguint);
            pw.set_biguint_target(&v_r_biguint_target[i], &r_biguint);
            pw.set_biguint_target(&v_s_biguint_target[i], &s_biguint);
            pw.set_biguint_target(&v_pk_x_biguint_target[i], &pk_x_biguint);
            pw.set_biguint_target(&v_pk_y_biguint_target[i], &pk_y_biguint);
        }
        //let prove_start_time = std::time::Instant::now();

        //let proof = std::hint::black_box(data.prove(pw).unwrap());
        // normal test
        let proof = data.prove(pw).unwrap();
        // test out pinned memory
        //let proof = data.prove_with_out_pinned_memory(pw).unwrap();
        // test out memory
        // let proof = data.prove_with_out_memory(pw).unwrap();
        //print!("{j}th prove costs time :{:?}",prove_start_time.elapsed() );

        println!("proof PIS {:?}", proof.public_inputs);
        data.verify(proof).unwrap();

        println!("-----------------------------{j}th finished----------------------------------------------");
    }

    // let proof = data.prove(pw).unwrap();

    // println!("proof PIS {:?}", proof.public_inputs);
    // data.verify(proof).unwrap();

    // println!("---------------------------------------------------------------------------");

    // let proof = data.prove(pw2).unwrap();

    // println!("proof PIS {:?}", proof.public_inputs);
    // data.verify(proof).unwrap();
}

// #[cfg(test)]
#[cfg(any(test, bench))]
pub mod tests {
    // use jemallocator::Jemalloc;

    // #[global_allocator]
    // static GLOBAL: Jemalloc = Jemalloc;
    use std::fs::{self, File};
    use std::io::prelude::*;
    use std::io::{BufReader, Write};

    use crate::ecdsa::curve::secp256k1;
    use crate::ecdsa::gadgets::biguint::WitnessBigUint;
    use crate::hash::keccak256;
    use anyhow::{Ok, Result};
    use plonky2::field::types::{PrimeField, Sample};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
    use plonky2::plonk::config::{
        GenericConfig, /*Poseidon2GoldilocksConfig,*/ PoseidonGoldilocksConfig,
    };
    use plonky2::util::serialization::{DefaultGateSerializer, DefaultGeneratorSerializer};
    use sha3::Sha3_256;

    use super::*;
    use crate::ecdsa::curve::curve_types::CurveScalar;
    use crate::ecdsa::curve::ecdsa::{
        sign_message, ECDSAPublicKey, ECDSASecretKey, ECDSASignature,
    };
    use crate::profiling_enable;

    fn test_ecdsa_circuit_with_config(config: CircuitConfig) -> Result<()> {
        profiling_enable();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        type Curve = Secp256K1;

        let mut builder = CircuitBuilder::<F, D>::new(config);

        let msg_target = builder.add_virtual_nonnative_target();
        let msg_biguint_target = builder.nonnative_to_canonical_biguint(&msg_target);

        // let pk_target = ECDSAPublicKeyTarget(builder.constant_affine_point(pk.0));
        // TODO: builder.constant_affine_point(pk.0) has an extra debug_assert!(!point.zero);
        let pk_target = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target());
        let pk_x_biguint_target = builder.nonnative_to_canonical_biguint(&pk_target.0.x);
        let pk_y_biguint_target = builder.nonnative_to_canonical_biguint(&pk_target.0.y);

        let r_target = builder.add_virtual_nonnative_target();
        let r_biguint_target = builder.nonnative_to_canonical_biguint(&r_target);

        let s_target = builder.add_virtual_nonnative_target();
        let s_biguint_target = builder.nonnative_to_canonical_biguint(&s_target);

        let sig_target = ECDSASignatureTarget {
            r: r_target,
            s: s_target,
        };

        verify_message_circuit(&mut builder, msg_target, sig_target, pk_target);

        dbg!(builder.num_gates());
        let data: plonky2::plonk::circuit_data::CircuitData<
            plonky2::field::goldilocks_field::GoldilocksField,
            PoseidonGoldilocksConfig,
            2,
        > = builder.build::<C>();

        for _ in 0..PROVE_RUN_TIMES {
            let mut pw = PartialWitness::new();

            let msg = Secp256K1Scalar::rand();

            let sk = ECDSASecretKey::<Curve>(Secp256K1Scalar::rand());
            let pk = ECDSAPublicKey((CurveScalar(sk.0) * Curve::GENERATOR_PROJECTIVE).to_affine());

            let sig = sign_message(msg, sk);

            let ECDSASignature { r, s } = sig;

            let msg_biguint = msg.to_canonical_biguint();
            let pk_x_biguint = pk.0.x.to_canonical_biguint();
            let pk_y_biguint = pk.0.y.to_canonical_biguint();
            let r_biguint = r.to_canonical_biguint();
            let s_biguint = s.to_canonical_biguint();

            pw.set_biguint_target(&msg_biguint_target, &msg_biguint);
            pw.set_biguint_target(&r_biguint_target, &r_biguint);
            pw.set_biguint_target(&s_biguint_target, &s_biguint);
            pw.set_biguint_target(&pk_x_biguint_target, &pk_x_biguint);
            pw.set_biguint_target(&pk_y_biguint_target, &pk_y_biguint);

            let proof = data.prove(pw).unwrap();
            println!("proof PIS {:?}", proof.public_inputs);
            println!("prove success!!!");
            assert!(data.verify(proof).is_ok());
        }
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_batch_ecdsa_circuit_narrow() -> Result<()> {
        test_batch_ecdsa_circuit_with_config(
            ECDSA_BATCH_SIZE,
            CircuitConfig::standard_ecc_config(),
        );
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_batch_ecdsa_cuda_circuit_narrow() -> Result<()> {
        test_batch_ecdsa_cuda_circuit_with_config(
            ECDSA_BATCH_SIZE,
            CircuitConfig::standard_ecc_config(),
        );
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_ecdsa_circuit_narrow() -> Result<()> {
        test_ecdsa_circuit_with_config(CircuitConfig::standard_ecc_config())
    }

    #[test]
    #[ignore]
    fn test_ecdsa_circuit_wide() -> Result<()> {
        test_ecdsa_circuit_with_config(CircuitConfig::wide_ecc_config())
    }
}
