use std::marker::PhantomData;

use ff::{Field, PrimeField};
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::{
    constants::KECCAK_LANE_SIZE,
    packed_chip::{
        decomposition::rotation::{get_dense_limb_coefficients, lane_limbs},
        utils::SpreadBits,
        PackedChip, PackedConfig,
    },
};

#[derive(Debug)]
enum ShouldFail {
    No,
    // try to use a full limb (no tag restriction) for the small ones
    UseBadResult(usize),
}

#[derive(Debug)]
struct TestRotationCircuit<F: PrimeField> {
    // input consists of a lane and a rotation
    inputs: Vec<(u64, usize)>,
    should_fail: ShouldFail,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for TestRotationCircuit<F> {
    type Config = PackedConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            inputs: vec![],
            should_fail: ShouldFail::No,
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

        layouter.assign_region(
            || "lane to spread limbs and rotate",
            |mut region| {
                // assign one decomposition per row
                self.inputs
                    .iter()
                    .enumerate()
                    .map(|(offset, &(input, rot))| {
                        // assign the spread word
                        packed_chip.assign_spread_decomposition(
                            &mut region,
                            2 * offset,
                            &Value::known(input),
                            rot,
                        )?;
                        // assign the rotation
                        packed_chip.assign_rotation_next_row(
                            &mut region,
                            2 * offset,
                            &Value::known(input),
                            rot,
                        )?;

                        if let ShouldFail::UseBadResult(i) = self.should_fail {
                            if i == offset {
                                let bad_value =
                                    SpreadBits::try_from_u64(input + 1, KECCAK_LANE_SIZE).unwrap();
                                region.assign_advice(
                                    || format!("assign false rotation result at input {}", i),
                                    packed_chip.config().decomposition_subconfig.dc_result_col,
                                    2 * i + 1,
                                    || Value::known(bad_value.clone()),
                                )?;
                            }
                        };
                        Ok(())
                    })
                    .collect::<Result<Vec<_>, Error>>()
            },
        )?;
        Ok(())
    }
}

#[test]
fn test_rotations_next_row() {
    let number_of_inputs = 10;

    // test a few random inputs
    let mut rng = ChaCha8Rng::from_entropy();
    let inputs: Vec<_> = (0..number_of_inputs)
        .map(|_| (rng.next_u64(), rng.gen_range(0..KECCAK_LANE_SIZE)))
        .collect();

    // run the circuit honestly
    let circuit = TestRotationCircuit::<Fp> {
        inputs: inputs.clone(),
        should_fail: ShouldFail::No,
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    prover.assert_satisfied();

    // use bad rotation result
    let i = rng.gen_range(0..number_of_inputs);
    let circuit = TestRotationCircuit::<Fp> {
        inputs: inputs.clone(),
        should_fail: ShouldFail::UseBadResult(i),
        _marker: PhantomData,
    };
    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };
    assert!(prover.verify().is_err());
}

#[test]
fn test_rotations() {
    let mut rng = ChaCha8Rng::from_entropy();

    let number_of_tests = 100;

    (0..number_of_tests).for_each(|_| {
        // sample a random lane
        let v = rng.next_u64();

        // test all possible rotations
        for rot in 0..KECCAK_LANE_SIZE {
            // get rotated value
            let rotated_v = v.rotate_right(rot as u32);

            // get limbs as field elements
            let limbs = lane_limbs(v, rot).into_iter().map(Fp::from);

            // get constants
            let constants = get_dense_limb_coefficients::<Fp>(rot, false);
            let rot_constants = get_dense_limb_coefficients::<Fp>(rot, true);

            // get the computed and expected values
            let computed_v =
                constants.iter().zip(limbs.clone()).fold(Fp::ZERO, |acc, (c, l)| acc + c * l);
            // get the expected value
            let expected_v = Fp::from(v);

            assert_eq!(computed_v, expected_v);

            // get the computed and expected values for the rotation
            let computed_rot =
                rot_constants.into_iter().zip(limbs).fold(Fp::ZERO, |acc, (c, l)| acc + c * l);
            // get the expected value
            let expected_rot = Fp::from(rotated_v);

            assert_eq!(computed_rot, expected_rot);
        }
    });
}
