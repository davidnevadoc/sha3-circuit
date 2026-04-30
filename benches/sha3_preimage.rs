#[macro_use]
extern crate criterion;

use std::{
    fs::File,
    io::{BufReader, Write},
    marker::PhantomData,
    path::Path,
};

use criterion::{BenchmarkId, Criterion};
use ff::PrimeField;
use midnight_curves::bls12_381::{Bls12, Fq as Fr};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk, prepare, Circuit, ConstraintSystem, Error, ProvingKey,
        VerifyingKey,
    },
    poly::{
        commitment::Guard,
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
    },
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha3_circuit::{
    instructions::Keccackf1600Instructions,
    packed_chip::{PackedChip, PackedConfig},
    sha3_256_gadget::Sha3_256,
};

fn criterion_benchmark(c: &mut Criterion) {
    // circuit that proves knowledge of some fixed size hash preimage
    #[derive(Debug, Clone)]
    struct Sha3PreimageCircuit<F: PrimeField> {
        preimage: Vec<u8>,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for Sha3PreimageCircuit<F> {
        type Config = PackedConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                preimage: Vec::new(),
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            PackedChip::from_scratch(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // create chip
            let packed_chip = PackedChip::<F>::new(&config);
            packed_chip.load_table(&mut layouter)?;

            // create gadget
            let sha3_gadget = Sha3_256::new(packed_chip);

            // compute the digest
            let preimage =
                self.preimage.iter().map(|b| Value::known(b).cloned()).collect::<Vec<_>>();
            sha3_gadget.digest(&mut layouter, &preimage[..])?;

            Ok(())
        }
    }

    fn key_and_circuit_gen(
        input_len: usize,
    ) -> (
        ParamsKZG<Bls12>,
        ProvingKey<Fr, KZGCommitmentScheme<Bls12>>,
        Sha3PreimageCircuit<Fr>,
    ) {
        let mut rng = ChaCha8Rng::from_entropy();

        // Read or create parameters
        let path = format!("./assets/keys/sha3_preimage_params_{}", input_len);
        let params_path = Path::new(&path);
        if File::open(params_path).is_err() {
            let min_k = PackedChip::<Fr>::min_k(input_len);
            let params = ParamsKZG::<Bls12>::unsafe_setup(min_k, &mut rng);
            let mut buf = Vec::new();

            params
                .write_custom(&mut buf, SerdeFormat::Processed)
                .expect("Failed to write parameters");
            let mut file = File::create(params_path).expect("Failed to create parameters");

            file.write_all(&buf[..]).expect("Failed to write parameters to file");
        }

        // Setup
        let params = File::open(params_path).expect("couldn't load params");
        let params: ParamsKZG<Bls12> =
            ParamsKZG::read_custom::<_>(&mut BufReader::new(params), SerdeFormat::Processed)
                .expect("Failed to read params");

        let preimage = vec![42u8; input_len];

        let circuit: Sha3PreimageCircuit<Fr> = Sha3PreimageCircuit {
            preimage,
            _marker: PhantomData,
        };

        // we do not use compressed selectors since they affect the vk size
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(vk.clone(), &circuit).expect("keygen_pk should not fail");
        (params, pk, circuit)
    }

    fn prover(
        circuit: Sha3PreimageCircuit<Fr>,
        params: &ParamsKZG<Bls12>,
        pk: &ProvingKey<Fr, KZGCommitmentScheme<Bls12>>,
    ) -> Vec<u8> {
        let rng = ChaCha8Rng::from_entropy();

        let mut transcript = CircuitTranscript::init();
        create_proof::<Fr, KZGCommitmentScheme<Bls12>, CircuitTranscript<blake2b_simd::State>, _>(
            params,
            pk,
            std::slice::from_ref(&circuit),
            0,
            &[&[]],
            &mut transcript,
            rng,
        )
        .expect("proof generation should not fail");
        transcript.finalize()
    }

    fn verifier(
        params: &ParamsKZG<Bls12>,
        vk: &VerifyingKey<Fr, KZGCommitmentScheme<Bls12>>,
        proof: &[u8],
    ) {
        let mut transcript = CircuitTranscript::init_from_bytes(proof);
        let res =
            prepare::<Fr, KZGCommitmentScheme<Bls12>, CircuitTranscript<blake2b_simd::State>>(
                vk,
                &[],
                &[&[]],
                &mut transcript,
            )
            .expect("Failed to prepare proof verifier");
        assert!(
            res.verify(&params.verifier_params()).is_ok(),
            "Failed to verify proof"
        );
    }

    let byte_lengths = vec![
        100usize, 200, 300, 400, 500, 750, 1000, 2000, 3000, 5000, 10000,
    ];

    for len in byte_lengths {
        let (params, pk, circuit) = key_and_circuit_gen(len);
        println!(
            "vk length: {} bytes",
            pk.get_vk().to_bytes(SerdeFormat::Processed).len()
        );

        let mut prover_group = c.benchmark_group(format!("plonk-prover: {} bytes", len));
        prover_group.sample_size(10);
        prover_group.bench_with_input(
            BenchmarkId::from_parameter(len),
            &(&params, &pk),
            |b, &(params, pk)| {
                b.iter(|| prover(circuit.clone(), params, pk));
            },
        );
        prover_group.finish();

        let (params, pk, circuit) = key_and_circuit_gen(len);
        let proof = prover(circuit.clone(), &params, &pk);

        println!("Proof length: {} bytes", proof.len());

        let mut verifier_group = c.benchmark_group(format!("plonk-verifier: {} bytes", len));

        verifier_group.sample_size(10);
        verifier_group.bench_with_input(
            BenchmarkId::from_parameter(len),
            &(&params, pk.get_vk(), &proof[..]),
            |b, &(params, vk, proof)| {
                b.iter(|| verifier(params, vk, proof));
            },
        );
        verifier_group.finish();
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
