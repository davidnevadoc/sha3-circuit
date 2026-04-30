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

use super::{compute_chi, compute_iota, compute_rho, compute_theta, KeccakState};
use crate::{
    constants::{KECCAK_NUM_LANES, KECCAK_WIDTH},
    packed_chip::{utils::SpreadBits, PackedChip, PackedConfig, MAX_BIT_LENGTH},
};

/// enum that defines which step we test
enum KeccakStep {
    RhoThetaIota,
    Chi,
}

/// Takes as input a keccak state a[i] and computes
/// in circuit the values rho(theta(a[i])
struct TestComputeStep<F: PrimeField> {
    inputs: Vec<KeccakState>,
    step: KeccakStep,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for TestComputeStep<F> {
    // we use an instance column to witness the expected result
    type Config = (PackedConfig, Column<Instance>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            inputs: Default::default(),
            step: KeccakStep::Chi,
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
        let assigned_states = packed_chip.assign_states(&mut layouter, self.inputs.as_slice())?;

        // compute the cs. we treat the i-th input as the i-th round
        let result = layouter.assign_region(
            || "compute theta",
            |mut region| {
                assigned_states
                    .iter()
                    .enumerate()
                    .map(|(n, state)| {
                        // compute rho(theta) or chi
                        match self.step {
                            KeccakStep::RhoThetaIota => {
                                packed_chip.compute_theta_rho(&mut region, n, state)
                            }
                            KeccakStep::Chi => packed_chip.compute_chi(&mut region, n, state, None),
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()
            },
        )?;

        // assign the public input
        result.iter().enumerate().try_for_each(|(i, assigned_state)| {
            assigned_state
                .inner
                .iter()
                .flat_map(|lanes| lanes.iter())
                .enumerate()
                .try_for_each(|(j, lane)| {
                    layouter.constrain_instance(lane.cell(), config.1, KECCAK_NUM_LANES * i + j)
                })
        })
    }
}

fn test_compute_step(step: KeccakStep) {
    let k = MAX_BIT_LENGTH as u32 + 1;

    let number_of_inputs = 25;

    // sample random inputs
    let mut rng = ChaCha8Rng::from_entropy();
    let mut inputs = vec![[[0u64; KECCAK_WIDTH]; KECCAK_WIDTH]; number_of_inputs];
    for input in inputs.iter_mut().take(number_of_inputs) {
        for lanes in input.iter_mut().take(KECCAK_WIDTH) {
            for lane in lanes.iter_mut().take(KECCAK_WIDTH) {
                *lane = rng.next_u64();
            }
        }
    }

    // create the keccak states
    let inputs = inputs.iter().map(KeccakState::from_lanes).collect::<Vec<_>>();

    // compute rho(theta(state)) and apply iota of "previous" round
    let mut outputs = inputs.clone();
    outputs.iter_mut().enumerate().for_each(|(r, state)| match step {
        KeccakStep::RhoThetaIota => {
            if r > 0 {
                compute_iota(state, r - 1);
            }
            compute_theta(state);
            compute_rho(state);
        }
        KeccakStep::Chi => {
            compute_chi(state);
        }
    });

    // spread the expected state and create the public inputs
    let expected_state = outputs
        .iter()
        .flat_map(|state| state.inner)
        .map(|lane| SpreadBits::try_from_u64(lane, 64).unwrap().to_field())
        .collect::<Vec<_>>();

    let circuit = TestComputeStep::<Fp> {
        inputs,
        step,
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![expected_state]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    prover.assert_satisfied();
}

#[test]
fn test_theta_rho_step() {
    test_compute_step(KeccakStep::RhoThetaIota);
}

#[test]
fn test_chi_step() {
    test_compute_step(KeccakStep::Chi);
}
