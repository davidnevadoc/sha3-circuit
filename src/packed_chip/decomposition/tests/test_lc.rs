use std::marker::PhantomData;

use ff::{Field, PrimeField};
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::packed_chip::{PackedChip, PackedConfig, MAX_BIT_LENGTH, NUM_LIMBS};
enum ShouldFail {
    // circuit is honestly generated
    No,
    // change j-th limb of i-th input
    BadLimb(usize, usize),
    // change i-th lc result
    BadResult(usize),
}

/// Takes as input (limb, coef, rot_coef) tuples and
/// performs the linear combinations
///     sum coef_i limb_i
struct TestLC<F: PrimeField> {
    inputs: Vec<[(F, F); NUM_LIMBS]>,
    should_fail: ShouldFail,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for TestLC<F> {
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
            || "assign linear combination",
            |mut region| {
                // in each row perform two lcs with input[i]
                self.inputs
                    .iter()
                    .enumerate()
                    .map(|(offset, &input)| {
                        // assign the limbs
                        for (j, (limb, _)) in input.iter().enumerate() {
                            region.assign_advice(
                                || format!("assign limb {}", j),
                                packed_chip.config().decomposition_subconfig.dc_advice_cols[j],
                                offset,
                                || Value::known(limb.to_owned()),
                            )?;
                        }

                        // compute and assign result
                        let res =
                            input.into_iter().fold(F::ZERO, |acc, (limb, coef)| acc + coef * limb);

                        let res = region.assign_advice(
                            || "assign result",
                            packed_chip.config().decomposition_subconfig.dc_result_col,
                            offset,
                            || Value::known(res),
                        )?;

                        // assign constnts for the re-composed word
                        let coefficients = input.map(|(_, c)| c);
                        packed_chip.assign_dc_constants(&mut region, offset, &coefficients)?;
                        // enable spread lookup selector

                        // Change assigned values in case the test should fail
                        match self.should_fail {
                            ShouldFail::No => (),
                            // change the j-th limb of the i-th input
                            ShouldFail::BadLimb(i, j) => {
                                if offset == i {
                                    // mess the limb by adding one
                                    let bad_value = self.inputs[i][j].0 + F::ONE;
                                    region.assign_advice(
                                        || format!("assign (false) limb {}", j),
                                        packed_chip.config().decomposition_subconfig.dc_advice_cols
                                            [j],
                                        offset,
                                        || Value::known(bad_value),
                                    )?;
                                }
                            }
                            ShouldFail::BadResult(i) => {
                                if offset == i {
                                    // Assign input + 1 in the lc result to force the
                                    // constraint to fail
                                    let bad_value = res.value().map(|&x| x + F::ONE);
                                    region.assign_advice(
                                        || "false lc result {}",
                                        packed_chip.config().decomposition_subconfig.dc_result_col,
                                        offset,
                                        || bad_value,
                                    )?;
                                }
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
fn test_lc_constraints() {
    let k = MAX_BIT_LENGTH as u32 + 1;

    let number_of_inputs = 10;

    // test a few random inputs
    let mut rng = ChaCha8Rng::from_entropy();
    let mut inputs = vec![[(Fp::default(), Fp::default()); NUM_LIMBS]; number_of_inputs];
    (0..number_of_inputs).for_each(|i| {
        (0..NUM_LIMBS).for_each(|j| {
            inputs[i][j].0 = Fp::random(&mut rng);
            inputs[i][j].1 = Fp::random(&mut rng);
        });
    });
    // run the circuit honestly
    let circuit = TestLC::<Fp> {
        inputs: inputs.clone(),
        should_fail: ShouldFail::No,
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    prover.assert_satisfied();

    // use malformed limbs
    let bad_input = rng.gen_range(0..number_of_inputs);
    let bad_col = rng.gen_range(0..NUM_LIMBS);
    let circuit = TestLC::<Fp> {
        inputs: inputs.clone(),
        should_fail: ShouldFail::BadLimb(bad_input, bad_col),
        _marker: PhantomData,
    };
    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };
    assert!(prover.verify().is_err());

    // use malformed result
    let bad_input = rng.gen_range(0..number_of_inputs);
    let circuit = TestLC::<Fp> {
        inputs: inputs.clone(),
        should_fail: ShouldFail::BadResult(bad_input),
        _marker: PhantomData,
    };
    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };
    assert!(prover.verify().is_err());
}
