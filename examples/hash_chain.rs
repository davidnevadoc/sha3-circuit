use std::marker::PhantomData;

use ff::PrimeField;
use midnight_curves::bls12_381::{Bls12, Fq as Fr};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk, prepare, Circuit, Column, ConstraintSystem, Error,
        Instance, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::Guard,
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
    },
    transcript::{CircuitTranscript, Transcript},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha3::{Digest, Sha3_256 as Sha3_256_CPU};
use sha3_circuit::{
    packed_chip::{PackedChip, PackedConfig},
    sha3_256_gadget::Sha3_256,
};

// PoK for the statement "L = {x | there exists w s.t. h(h(...h(w))..) = x}"
// where h is the sha3-256 hash function and is applied 10 times

#[derive(Debug, Clone)]
struct HashChain10<F: PrimeField> {
    w: [u8; 32],
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for HashChain10<F> {
    // we use an instance column to put the result x
    type Config = (PackedConfig, Column<Instance>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        let packed_config = PackedChip::from_scratch(meta);
        (packed_config, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // create chip
        let packed_chip = PackedChip::<F>::new(&config.0);
        packed_chip.load_table(&mut layouter)?;

        // create gadget
        let sha3_gadget = Sha3_256::new(packed_chip);

        // prepare the first digest input
        let w = self.w.iter().map(|b| Value::known(b).cloned()).collect::<Vec<_>>();

        // do the first hash. The input is assigned freely by the prover and corresponds
        // to the value w
        let (_, assigned_output) = sha3_gadget.digest(&mut layouter, &w[..])?;

        let mut previous_output = assigned_output;

        // iteratively hash 9 more times
        for i in 0..9 {
            // prepare the next input values which are the previous output values
            let hash_input = previous_output.clone().map(|assigned_dense| {
                assigned_dense.value().map(|dense_bits| dense_bits.to_lane() as u8)
            });

            // hash in circuit the new input
            let (assigned_input, assigned_output) =
                sha3_gadget.digest(&mut layouter, &hash_input[..])?;

            // copy constrain the new input to equal the previous output
            layouter.assign_region(
                || {
                    format!(
                        "equality constrains for the hash chaining in iteration {}",
                        i
                    )
                },
                |mut region| {
                    previous_output.iter().zip(assigned_input.iter()).try_for_each(
                        |(prev, next)| region.constrain_equal(prev.cell(), next.cell()),
                    )
                },
            )?;

            // update the previous output for the next iteration
            previous_output = assigned_output
        }

        // witness the public input x which is the final output
        previous_output
            .iter()
            .enumerate()
            .try_for_each(|(j, bytes)| layouter.constrain_instance(bytes.cell(), config.1, j))?;

        Ok(())
    }
}

// helper function to implement sha3-256 digest in cpu
fn digest_cpu(input: &[u8]) -> Vec<u8> {
    let mut hasher = Sha3_256_CPU::new();
    hasher.update(input);
    hasher.finalize().into_iter().collect::<Vec<_>>()
}

// keygen
#[allow(clippy::type_complexity)]
fn keygen() -> (
    ParamsKZG<Bls12>,
    ProvingKey<Fr, KZGCommitmentScheme<Bls12>>,
    VerifyingKey<Fr, KZGCommitmentScheme<Bls12>>,
) {
    let mut rng = ChaCha8Rng::from_entropy();

    let params = ParamsKZG::<Bls12>::unsafe_setup(16, &mut rng);

    // we create the keys with an arbitrary witness, here the all zero witness
    let circuit: HashChain10<Fr> = HashChain10 {
        w: [0; 32],
        _marker: PhantomData,
    };

    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(vk.clone(), &circuit).expect("keygen_pk should not fail");

    (params, pk, vk)
}

// prover
fn prover(
    circuit: HashChain10<Fr>,
    params: &ParamsKZG<Bls12>,
    pk: &ProvingKey<Fr, KZGCommitmentScheme<Bls12>>,
) -> Vec<u8> {
    let rng = ChaCha8Rng::from_entropy();

    // compute the hash in cpu to prepare the public input
    let pi = (0..10)
        .fold(circuit.w.to_vec(), |acc, _| digest_cpu(&acc[..]))
        .iter()
        .map(|b| Fr::from(*b as u64))
        .collect::<Vec<_>>();

    let mut transcript = CircuitTranscript::init();
    create_proof::<Fr, KZGCommitmentScheme<Bls12>, CircuitTranscript<blake2b_simd::State>, _>(
        params,
        pk,
        std::slice::from_ref(&circuit),
        0,
        &[&[pi.as_slice()]],
        &mut transcript,
        rng,
    )
    .expect("proof generation should not fail");
    transcript.finalize()
}

// verifier
fn verifier(
    params: &ParamsKZG<Bls12>,
    pi: &[Fr],
    vk: &VerifyingKey<Fr, KZGCommitmentScheme<Bls12>>,
    proof: &[u8],
) {
    let mut transcript = CircuitTranscript::init_from_bytes(proof);
    let res = prepare::<Fr, KZGCommitmentScheme<Bls12>, CircuitTranscript<blake2b_simd::State>>(
        vk,
        &[&[]],
        &[&[pi]],
        &mut transcript,
    )
    .expect("Failed to prepare proof verifier");

    assert!(
        res.verify(&params.verifier_params()).is_ok(),
        "Failed to verify proof"
    );
}

fn main() {
    let (params, pk, vk) = keygen();

    let circuit = HashChain10 {
        w: [42; 32],
        _marker: PhantomData,
    };

    // compute the hash in cpu (this corresponds to the statement)
    let pi = (0..10)
        .fold(circuit.w.to_vec(), |acc, _| digest_cpu(&acc[..]))
        .iter()
        .map(|b| Fr::from(*b as u64))
        .collect::<Vec<_>>();

    // create the proof
    let proof = prover(circuit.clone(), &params, &pk);

    // verify the proof
    verifier(&params, pi.as_slice(), &vk, &proof);
}
