use std::marker::PhantomData;

use ff::PrimeField;
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error, Selector},
};
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::packed_chip::{utils::SpreadBits, PackedChip, PackedConfig};

enum ShouldFail {
    // circuit is honestly generated
    No,
    // change j-th term of i-th input
    BadTerm(usize, usize),
    // change i-th result
    BadResult(usize),
}

#[derive(Debug, Clone)]
enum Gate {
    C,
    Theta,
    Chi,
}

/// Takes as input u64 vectors and computes for each the
/// constrain defined by gate
struct TestAuxGateCircuit<F: PrimeField> {
    inputs: Vec<Vec<u64>>,
    should_fail: ShouldFail,
    gate: Gate,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> TestAuxGateCircuit<F> {
    fn get_selector(&self, config: &PackedConfig) -> Selector {
        match self.gate {
            Gate::C => config.lc_subconfig.q_c,
            Gate::Theta => config.lc_subconfig.q_theta,
            Gate::Chi => config.lc_subconfig.q_chi,
        }
    }

    fn get_terms_and_result(&self, i: usize) -> Vec<SpreadBits> {
        let vs = self.inputs[i].clone();
        let nr_terms = match self.gate.clone() {
            Gate::Chi | Gate::Theta => 4,
            Gate::C => 6,
        };
        match self.gate {
            // in both cases we need to add all elements in the two or three rows and
            // compare to result
            Gate::C | Gate::Theta => {
                let mut spread_vs = vs
                    .iter()
                    .take(nr_terms)
                    .map(|&v| SpreadBits::try_from_u64(v, 64).unwrap())
                    .collect::<Vec<_>>();
                let init = SpreadBits::try_from_u64(vs[0], 64).unwrap();
                let result = spread_vs.iter().skip(1).fold(init, |acc, v| acc.try_add(v).unwrap());
                spread_vs.push(result);
                spread_vs
            }
            // we compute the chi constraint
            Gate::Chi => {
                let mut spread_vs = vs
                    .iter()
                    .map(|&v| SpreadBits::try_from_u64(v, 64).unwrap())
                    .collect::<Vec<_>>();

                let terms = [
                    spread_vs[0].mul2().unwrap(),
                    spread_vs[1].mul2().unwrap(),
                    spread_vs[2].negate().unwrap(),
                    spread_vs[3].clone(),
                ];
                let init = terms[0].clone();
                let result = terms.iter().skip(1).fold(init, |acc, v| acc.try_add(v).unwrap());
                spread_vs.push(result);
                spread_vs
            }
        }
    }
}

impl<F: PrimeField> Circuit<F> for TestAuxGateCircuit<F> {
    type Config = PackedConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            inputs: vec![],
            should_fail: ShouldFail::No,
            gate: Gate::C,
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
            || "assign values",
            |mut region| {
                let rows_per_gate = match self.gate.clone() {
                    Gate::C => 3,
                    _ => 2,
                };
                (0..self.inputs.len())
                    .map(|i| {
                        let values_to_assign = self.get_terms_and_result(i);
                        // enable the appropriate selector
                        let selector = self.get_selector(packed_chip.config());
                        selector.enable(&mut region, rows_per_gate * i)?;

                        // assign the values
                        values_to_assign
                            .iter()
                            .take(rows_per_gate * 2)
                            .enumerate()
                            .map(|(j, v)| {
                                // assign the values at the current offset
                                region.assign_advice(
                                    || format!("assigning term {}", j),
                                    packed_chip.config().lc_subconfig.advice[j % 2],
                                    rows_per_gate * i + j / 2,
                                    || Value::known(v.clone()),
                                )
                            })
                            .collect::<Result<Vec<_>, Error>>()?;
                        // assign the result
                        region.assign_advice(
                            || "assigning result in bootstrap acc column",
                            packed_chip.config().bootstrap_subconfig.bootstrap_acc_col,
                            rows_per_gate * i + rows_per_gate - 1,
                            || Value::known(values_to_assign.last().unwrap().clone()),
                        )
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                match self.should_fail {
                    ShouldFail::No => (),
                    ShouldFail::BadTerm(i, j) => {
                        region.assign_advice(
                            || format!("assigning bad term {} at input {}", j, i),
                            packed_chip.config().lc_subconfig.advice[j % 2],
                            rows_per_gate * i + j / 2,
                            || Value::known(F::from(42)),
                        )?;
                    }
                    ShouldFail::BadResult(i) => {
                        region.assign_advice(
                            || "assigning result",
                            packed_chip.config().bootstrap_subconfig.bootstrap_acc_col,
                            rows_per_gate * i + rows_per_gate - 1,
                            || Value::known(F::from(42)),
                        )?;
                    }
                };
                Ok(())
            },
        )
    }
}

fn test_gate_helper(gate: Gate) {
    let number_of_inputs = 10;

    // test a few random inputs
    let mut rng = ChaCha8Rng::from_entropy();

    // always take 6 inputs and keep four for the theta, chi gates
    let inputs: Vec<_> = (0..number_of_inputs)
        // always sample six and ignore the last when not needed
        .map(|_| (0..6).map(|_| rng.next_u64()).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let circuit = TestAuxGateCircuit::<Fp> {
        inputs: inputs.clone(),
        gate: gate.clone(),
        should_fail: ShouldFail::No,
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    prover.assert_satisfied();

    // negative tests
    let number_of_terms = match gate {
        Gate::C => 6,
        _ => 4,
    };

    // Change a random term
    let i = rng.gen_range(0..number_of_inputs);
    let j = rng.gen_range(0..number_of_terms);

    let circuit = TestAuxGateCircuit::<Fp> {
        inputs: inputs.clone(),
        gate: gate.clone(),
        should_fail: ShouldFail::BadTerm(i, j),
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    assert!(prover.verify().is_err());

    // Change a result
    let i = rng.gen_range(0..number_of_inputs);

    let circuit = TestAuxGateCircuit::<Fp> {
        inputs: inputs.clone(),
        gate,
        should_fail: ShouldFail::BadResult(i),
        _marker: PhantomData,
    };

    let prover = match MockProver::run(&circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    assert!(prover.verify().is_err());
}

#[test]
fn test_c_gate() {
    test_gate_helper(Gate::C)
}

#[test]
fn test_theta_gate() {
    test_gate_helper(Gate::Theta)
}

#[test]
fn test_chi_gate() {
    test_gate_helper(Gate::Chi)
}
