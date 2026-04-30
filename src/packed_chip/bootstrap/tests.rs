use std::marker::PhantomData;

use ff::{Field, PrimeField};
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::packed_chip::{
    bootstrap::assign_bootstrap::BPart, utils::SpreadBits, PackedChip, PackedConfig, MAX_BIT_LENGTH,
};

mod test_bootstrap_gate {
    use midnight_proofs::circuit::Chip;
    use rand::Rng;

    use super::*;

    enum ShouldFail {
        // circuit is honestly generated
        No,
        // change the cell in row i, j
        BadCell(usize, usize),
    }
    /// Takes as input vectors [F; E] and computes for each the value:
    /// v = sum_{i=0}^E-1 2^{E-i+1} v_i
    struct TestBootstrapGate<F: PrimeField, const E: usize> {
        inputs: Vec<[F; E]>,
        should_fail: ShouldFail,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField, const E: usize> Circuit<F> for TestBootstrapGate<F, E> {
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
                || "assign values",
                |mut region| {
                    self.inputs
                        .iter()
                        .enumerate()
                        .map(|(i, v)| {
                            // comupte the intermediate results for the acc column
                            let mut acc_vs = [F::ZERO; E];
                            acc_vs[0] = v[0];
                            for j in 1..E {
                                // acc_next = 2 acc_prev + part
                                acc_vs[j] = F::from(2) * acc_vs[j - 1] + v[j];
                            }

                            // assign the correct values
                            let assigned = (0..E)
                                .map(|j| {
                                    // enable the selector in all but last row
                                    let offset = E * i + j;
                                    if j != E - 1 {
                                        packed_chip
                                            .config()
                                            .bootstrap_subconfig
                                            .q_bootstrap
                                            .enable(&mut region, offset)?;
                                    }
                                    // assign the values at the current offset
                                    region.assign_advice(
                                        || format!("assigning part {}", j),
                                        packed_chip.config().bootstrap_subconfig.part_col,
                                        offset,
                                        || Value::known(v[j]),
                                    )?;
                                    region.assign_advice(
                                        || format!("assigning acc {}", j),
                                        packed_chip.config().bootstrap_subconfig.bootstrap_acc_col,
                                        offset,
                                        || Value::known(acc_vs[j]),
                                    )
                                })
                                .collect::<Result<Vec<_>, Error>>()?;
                            Ok(assigned)
                        })
                        .collect::<Result<Vec<_>, Error>>()?;
                    match self.should_fail {
                        ShouldFail::No => (),
                        ShouldFail::BadCell(i, 0) => {
                            region.assign_advice(
                                || format!("assigning bad part cell at row {}", i),
                                packed_chip.config().bootstrap_subconfig.part_col,
                                i,
                                || Value::known(F::from(42)),
                            )?;
                        }
                        ShouldFail::BadCell(i, 1) => {
                            region.assign_advice(
                                || format!("assigning bad acc cell at row {}", i),
                                packed_chip.config().bootstrap_subconfig.bootstrap_acc_col,
                                i,
                                || Value::known(F::from(42)),
                            )?;
                        }
                        _ => unreachable!(),
                    };
                    Ok(())
                },
            )
        }
    }

    fn test_bootstrap_gate_helper<const E: usize>() {
        let k = MAX_BIT_LENGTH as u32 + 1;

        let number_of_inputs = 10;

        // test a few random inputs
        let mut rng = ChaCha8Rng::from_entropy();
        let inputs: Vec<_> = (0..number_of_inputs)
            .map(|_| (0..E).map(|_| Fp::random(&mut rng)).collect::<Vec<_>>().try_into().unwrap())
            .collect::<Vec<[Fp; E]>>();

        let circuit = TestBootstrapGate::<Fp, E> {
            inputs: inputs.clone(),
            should_fail: ShouldFail::No,
            _marker: PhantomData,
        };

        let prover = match MockProver::run(&circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        prover.assert_satisfied();

        // negative tests
        // Change the part column. Here, the first cell is irrelevant
        let bad_input = rng.gen_range(0..number_of_inputs);
        let bad_input_row = rng.gen_range(1..E);
        let bad_row = bad_input * E + bad_input_row;

        let circuit = TestBootstrapGate::<Fp, E> {
            inputs: inputs.clone(),
            should_fail: ShouldFail::BadCell(bad_row, 0),
            _marker: PhantomData,
        };

        let prover = match MockProver::run(&circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert!(prover.verify().is_err());

        // negative tests
        // Change the acc column
        let bad_input = rng.gen_range(0..number_of_inputs);
        let bad_input_row = rng.gen_range(0..E);
        let bad_row = bad_input * E + bad_input_row;

        let circuit = TestBootstrapGate::<Fp, E> {
            inputs: inputs.clone(),
            should_fail: ShouldFail::BadCell(bad_row, 1),
            _marker: PhantomData,
        };

        let prover = match MockProver::run(&circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert!(prover.verify().is_err());
    }

    #[test]
    fn test_bootstrap_gate_2() {
        test_bootstrap_gate_helper::<2>();
    }

    #[test]
    fn test_bootstrap_gate_3() {
        test_bootstrap_gate_helper::<3>();
    }

    #[test]
    fn test_bootstrap_gate_10() {
        test_bootstrap_gate_helper::<10>();
    }
}

mod test_bootstrap_assignment {

    use ff::PrimeField;
    use midnight_curves::Fq as Fp;

    use super::*;

    /// Takes as input vectors of u64 words, combines them to SpreadBits  and
    /// bootstraps the result
    struct TestBootstrap<F: PrimeField, const E: usize> {
        inputs: Vec<Vec<u64>>,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField, const E: usize> Circuit<F> for TestBootstrap<F, E> {
        type Config = (PackedConfig, Column<Instance>);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: vec![],
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

            let results = layouter.assign_region(
                || "assign the results of bootstrap",
                // compute and assign the spread_xor
                |mut region| {
                    let xors = self
                        .inputs
                        .iter()
                        .map(|input| {
                            // compute the spread bits
                            let mut value =
                                input.iter().map(|&v| SpreadBits::try_from_u64(v, 64).unwrap());
                            let initial = value.next().unwrap();
                            value.fold(initial, |acc, v| acc.try_add(&v).unwrap())
                        })
                        .collect::<Vec<_>>();

                    // bootstrap the xors
                    let res = xors
                        .iter()
                        .enumerate()
                        .map(|(i, x)| match E {
                            2 => packed_chip.assign_bootstrap2(
                                &mut region,
                                2 * i,
                                &Value::known(x.clone()),
                                1,
                                BPart::L,
                            ),
                            3 => packed_chip.assign_bootstrap3(
                                &mut region,
                                3 * i,
                                &Value::known(x.clone()),
                                1,
                                BPart::L,
                            ),
                            _ => panic!(),
                        })
                        .collect::<Result<Vec<_>, Error>>();
                    res
                },
            )?;
            results.iter().enumerate().try_for_each(|(j, res)| {
                layouter.constrain_instance(res.cell(), config.1, j)?;
                Ok(())
            })
        }
    }

    fn test_bootstrap_helper<const E: usize>() {
        let k = MAX_BIT_LENGTH as u32 + 1;

        let number_of_inputs = 15;
        let xor_size = match E {
            // maximum number of XORs in two rows
            2 => 3,
            // maximum number of XORs in three rows
            3 => 6,
            _ => panic!(),
        };

        // test a few random inputs
        let mut rng = ChaCha8Rng::from_entropy();
        let inputs: Vec<_> = (0..number_of_inputs)
            .map(|_| (0..xor_size).map(|_| rng.next_u64()).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let results = inputs
            .iter()
            .map(|input| {
                let xor = input.iter().fold(0u64, |acc, x| acc ^ x);
                SpreadBits::try_from_u64(xor, 64).unwrap().to_field()
            })
            .collect::<Vec<_>>();

        let circuit = TestBootstrap::<Fp, E> {
            inputs: inputs.clone(),
            _marker: PhantomData,
        };

        let prover = match MockProver::run(&circuit, vec![results]) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        prover.assert_satisfied();
    }

    #[test]
    fn test_bootstrap2() {
        test_bootstrap_helper::<2>();
    }

    #[test]
    fn test_bootstrap3() {
        test_bootstrap_helper::<3>();
    }
}
