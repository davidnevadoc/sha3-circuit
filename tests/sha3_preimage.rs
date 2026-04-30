use std::marker::PhantomData;

use ff::PrimeField;
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha3::{Digest, Keccak256 as Keccak256Cpu, Sha3_256 as Sha3_256_CPU};
use sha3_circuit::{
    packed_chip::{PackedChip, PackedConfig},
    sha3_256_gadget::{Keccak256, Sha3_256},
};

// Which version will be tested
#[derive(Debug, Clone, Copy)]
enum HashMode {
    Sha3_256,
    Keccak256,
}

struct TestPreimage<F: PrimeField> {
    preimage: Vec<u8>,
    hash_mode: HashMode,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for TestPreimage<F> {
    // we use an instance column to witness the expected result
    type Config = (PackedConfig, Column<Instance>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            preimage: Vec::new(),
            hash_mode: HashMode::Sha3_256,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let packed_config = PackedChip::from_scratch(meta);
        let instance = meta.instance_column();
        meta.enable_equality(instance);
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
        let sha3_gadget = Sha3_256::new(packed_chip.clone());
        let keccak_gadget = Keccak256::new(packed_chip);

        // wrap input to Value
        let preimage = self.preimage.iter().map(|b| Value::known(b).cloned()).collect::<Vec<_>>();

        // compute the digest
        let (_input, output) = match self.hash_mode {
            HashMode::Sha3_256 => sha3_gadget.digest(&mut layouter, &preimage[..]),
            HashMode::Keccak256 => keccak_gadget.digest(&mut layouter, &preimage[..]),
        }?;

        // assign the digest bytes as public input
        output
            .iter()
            .enumerate()
            .try_for_each(|(j, bytes)| layouter.constrain_instance(bytes.cell(), config.1, j))
    }
}

fn test_preimage(mode: HashMode) {
    const KECCAK_ABSORB_BYTES: usize = 136;

    let mut rng = ChaCha8Rng::from_entropy();

    // tested sizes
    let sizes = [
        0usize,
        1,
        100,
        KECCAK_ABSORB_BYTES - 2,
        KECCAK_ABSORB_BYTES - 1,
        KECCAK_ABSORB_BYTES,
        KECCAK_ABSORB_BYTES + 1,
        KECCAK_ABSORB_BYTES + 2,
        3 * KECCAK_ABSORB_BYTES,
        3 * KECCAK_ABSORB_BYTES + 1,
        3 * KECCAK_ABSORB_BYTES + 100,
        3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES - 2,
        3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES - 1,
        3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES,
        3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES + 1,
        3 * KECCAK_ABSORB_BYTES + KECCAK_ABSORB_BYTES + 2,
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
        rng.gen_range(0..5 * KECCAK_ABSORB_BYTES),
    ];

    // sample random inputs for the above sizes

    let inputs = sizes
        .iter()
        .map(|&size| (0..size).map(|_| rng.gen()).collect::<Vec<u8>>())
        .collect::<Vec<_>>();

    let outputs = inputs
        .iter()
        .map(|bytes| {
            let result = match mode {
                HashMode::Sha3_256 => {
                    let mut hasher = Sha3_256_CPU::new();
                    hasher.update(bytes);
                    hasher.finalize()
                }
                HashMode::Keccak256 => {
                    let mut hasher = Keccak256Cpu::new();
                    hasher.update(bytes);
                    hasher.finalize()
                }
            };
            result.iter().map(|b| Fp::from(*b as u64)).collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // run the proof for each input/output pair
    inputs.iter().zip(outputs.iter()).for_each(|(preimage, digest)| {
        let circuit = TestPreimage::<Fp> {
            preimage: preimage.clone(),
            hash_mode: mode,
            _marker: PhantomData,
        };

        let prover = match MockProver::run(&circuit, vec![digest.clone()]) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        prover.assert_satisfied();
    });
}

#[test]
fn test_sha3_preimage() {
    test_preimage(HashMode::Sha3_256);
}

#[test]
fn test_keccak_preimage() {
    test_preimage(HashMode::Keccak256);
}
