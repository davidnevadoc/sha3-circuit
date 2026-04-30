use std::marker::PhantomData;

use ff::PrimeField;
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use super::KeccakState;
use crate::{
    constants::KECCAK_WIDTH,
    instructions::Keccackf1600Instructions,
    packed_chip::{
        keccakf_operations::tests::compute_keccakf, utils::SpreadBits, PackedChip, PackedConfig,
    },
};

/// Takes as input a keccak state and computes in circuit the state
/// after applying the keccak-f permutation a fixed number of times
struct TestComputeKeccakf<F: PrimeField> {
    input: KeccakState,
    repetitions: usize,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for TestComputeKeccakf<F> {
    // we use an instance column to witness the expected result
    type Config = (PackedConfig, Column<Instance>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            input: Default::default(),
            repetitions: Default::default(),
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

        // first we assign the input state
        let state = &self.input;
        let states = packed_chip.assign_states(&mut layouter, &[state.clone()])?;
        let initial = states[0].clone();

        // compute the keccakf in different regions
        let result = (0..self.repetitions).try_fold(initial, |old_state, _rep| {
            packed_chip.keccakf(&mut layouter, &old_state)
        })?;

        // assign the result as public input
        result
            .inner
            .iter()
            .flat_map(|lanes| lanes.iter())
            .enumerate()
            .try_for_each(|(j, lane)| layouter.constrain_instance(lane.cell(), config.1, j))
    }
}

#[test]
fn test_compute_keccakf() {
    let repetitions = 15;
    let k = 16;

    // random initial state
    let mut rng = ChaCha8Rng::from_entropy();
    let mut input = [[0u64; KECCAK_WIDTH]; KECCAK_WIDTH];
    for lanes in input.iter_mut().take(KECCAK_WIDTH) {
        for lane in lanes.iter_mut().take(KECCAK_WIDTH) {
            *lane = rng.next_u64();
        }
    }
    let input = KeccakState::from_lanes(&input);

    let mut state = input.clone();

    // compute expected result off circuit
    (0..repetitions).for_each(|_| compute_keccakf(&mut state));

    let expected = state
        .inner
        .iter()
        .map(|lane| SpreadBits::try_from_u64(*lane, 64).unwrap().to_field())
        .collect::<Vec<_>>();

    let circuit = TestComputeKeccakf::<Fp> {
        input,
        repetitions,
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![expected]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    prover.assert_satisfied();
}
