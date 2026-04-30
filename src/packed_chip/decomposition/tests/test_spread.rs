mod spread_from_u64 {
    use std::marker::PhantomData;

    use ff::PrimeField;
    use midnight_curves::Fq as Fp;
    use midnight_proofs::{
        circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
    };
    use rand::{Rng, RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use crate::{
        constants::KECCAK_LANE_SIZE,
        packed_chip::{
            decomposition::rotation::limb_size_tags, utils::SpreadBits, PackedChip, PackedConfig,
            LAST_FIXED_LIMB_LENGTH, MAX_BIT_LENGTH, NUM_FULL_LIMBS, NUM_LIMBS,
        },
    };

    #[derive(Debug)]
    enum ShouldFail {
        No,
        // limb j of input i is out of bounds
        LimbOutOfBound(usize, usize),
        // try to use a full limb (no tag restriction) for the small ones
        UseBigLimb(usize, usize),
    }

    #[derive(Debug)]
    struct TestSpreadRangeCircuit<F: PrimeField> {
        // input consists of a lane and a rotation
        inputs: Vec<(u64, usize)>,
        should_fail: ShouldFail,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for TestSpreadRangeCircuit<F> {
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
                || "lane to spread limbs",
                |mut region| {
                    // assign one decomposition per row
                    self.inputs
                        .iter()
                        .enumerate()
                        .map(|(offset, &(input, rot))| {
                            // assign the limbs and the result
                            // we use assign_spread_limbs_unchecked to not constraint
                            // the lc constraint and catch failures in the rangecheck
                            packed_chip.assign_spread_limbs(
                                &mut region,
                                offset,
                                &Value::known(input),
                                rot,
                            )?;
                            // Change assigned values in case the test should fail. We force a limb
                            // to be out of bounds
                            if let ShouldFail::LimbOutOfBound(i, j) = self.should_fail {
                                if i == offset {
                                    // make the i-th limb exceed the bound by setting it 2^{3*bound}
                                    let tags = limb_size_tags(rot);
                                    // bounds for full limbs, lo limb and small limbs
                                    let bounds = [MAX_BIT_LENGTH, LAST_FIXED_LIMB_LENGTH]
                                        .iter()
                                        .chain(tags.iter())
                                        .map(|bound|
                                        // compute 2^tag and spread it. The pair (tag, bound)
                                        // should *not* be on the lookup table
                                            SpreadBits::try_from_u64(1 << bound, bound + 1)
                                                .unwrap()
                                                .to_field::<F>())
                                        .collect::<Vec<_>>();
                                    // choose the appropriate value based on limb index j
                                    const FULL_INDEX: usize = NUM_FULL_LIMBS - 1;
                                    const LO_INDEX: usize = NUM_FULL_LIMBS;
                                    const SMALL_INDEX_1: usize = NUM_FULL_LIMBS + 1;
                                    const SMALL_INDEX_2: usize = NUM_FULL_LIMBS + 2;
                                    let bad_value: F = match j {
                                        0..=FULL_INDEX => bounds[0],
                                        LO_INDEX => bounds[1],
                                        SMALL_INDEX_1 => bounds[2],
                                        SMALL_INDEX_2 => bounds[3],
                                        _ => unreachable!(),
                                    };
                                    // reassign out-of-bounds limb i
                                    region.assign_advice(
                                        || format!("assign (false) limb {}", j),
                                        packed_chip.config().decomposition_subconfig.dc_advice_cols
                                            [j],
                                        offset,
                                        || Value::known(bad_value),
                                    )?;
                                }
                            };
                            if let ShouldFail::UseBigLimb(i, j) = self.should_fail {
                                if i == offset {
                                    // make one of the small limbs or LO limb be MAX_BIT_LENGTH
                                    // long) in an attepmt to use a value in the table but with
                                    // unchecked tag We use a MAX_BIT_LENGTH bad limb
                                    let bad_value: F = SpreadBits::try_from_u64(
                                        1 << (MAX_BIT_LENGTH - 1),
                                        MAX_BIT_LENGTH,
                                    )
                                    .unwrap()
                                    .to_field::<F>();
                                    // reassign out-of-bounds limb i
                                    region.assign_advice(
                                        || format!("assign (false) limb {}", j),
                                        packed_chip.config().decomposition_subconfig.dc_advice_cols
                                            [j],
                                        offset,
                                        || Value::known(bad_value),
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

    #[derive(Debug)]
    // tesing the final decomposition. We don't do negative tests since the linear
    // combination constraints are tested in
    // [`crate::decomposition::linear_combination`]
    struct TestSpreadDecompositionCircuit<F: PrimeField> {
        // input consists of a lane and a rotation
        inputs: Vec<(u64, usize)>,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for TestSpreadDecompositionCircuit<F> {
        type Config = (PackedConfig, Column<Instance>, Column<Instance>);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: vec![],
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let instance_rotated = meta.instance_column();
            meta.enable_equality(instance_rotated);
            let packed_config = PackedChip::from_scratch(meta);
            (packed_config, instance, instance_rotated)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // create chip
            let packed_chip = PackedChip::<F>::new(&config.0);
            packed_chip.load_table(&mut layouter)?;

            let result = layouter.assign_region(
                || "lane to spread limbs",
                |mut region| {
                    // decompose each input
                    self.inputs
                        .iter()
                        .enumerate()
                        .map(|(offset, &(input, rot))| {
                            // assign the limbs and the result
                            let assigned = packed_chip.assign_spread_decomposition(
                                &mut region,
                                2 * offset,
                                &Value::known(input),
                                rot,
                            )?;
                            let res = assigned.assigned_result;
                            Ok(res)
                        })
                        .collect::<Result<Vec<_>, Error>>()
                },
            )?;
            // constraint the result to match the expected given as public input
            result
                .iter()
                .enumerate()
                .try_for_each(|(i, v)| layouter.constrain_instance(v.cell(), config.1, i))
        }
    }

    #[test]
    fn test_spread_limb_ranges() {
        let k = MAX_BIT_LENGTH as u32 + 1;

        let number_of_inputs = 10;

        // test a few random inputs
        let mut rng = ChaCha8Rng::from_entropy();
        let inputs: Vec<_> = (0..number_of_inputs)
            .map(|_| (rng.next_u64(), rng.gen_range(0..KECCAK_LANE_SIZE)))
            .collect();

        // run the circuit honestly
        let circuit = TestSpreadRangeCircuit::<Fp> {
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
        (0..NUM_LIMBS).for_each(|j| {
            let i = rng.gen_range(0..number_of_inputs);
            let circuit = TestSpreadRangeCircuit::<Fp> {
                inputs: inputs.clone(),
                should_fail: ShouldFail::LimbOutOfBound(i, j),
                _marker: PhantomData,
            };
            let prover = match MockProver::run(&circuit, vec![]) {
                Ok(prover) => prover,
                Err(e) => panic!("{e:#?}"),
            };
            assert!(prover.verify().is_err());
        });

        // use "untagged" limbs for the small limbs and the LO limb if it is not of full
        // length
        let number_of_non_full_limbs = 2 + if LAST_FIXED_LIMB_LENGTH != MAX_BIT_LENGTH {
            1
        } else {
            0
        };
        (NUM_LIMBS - number_of_non_full_limbs..NUM_LIMBS).for_each(|j| {
            let i = rng.gen_range(0..number_of_inputs);
            let circuit = TestSpreadRangeCircuit::<Fp> {
                inputs: inputs.clone(),
                should_fail: ShouldFail::UseBigLimb(i, j),
                _marker: PhantomData,
            };
            let prover = match MockProver::run(&circuit, vec![]) {
                Ok(prover) => prover,
                Err(e) => panic!("{e:#?}"),
            };
            assert!(prover.verify().is_err());
        });
    }

    #[test]
    fn test_spread_decomposition() {
        let k = MAX_BIT_LENGTH as u32 + 1;

        let number_of_inputs = 10;

        // test a few random inputs
        let mut rng = ChaCha8Rng::from_entropy();
        let inputs: Vec<_> = (0..number_of_inputs)
            // input, rotation pairs
            .map(|_| (rng.next_u64(), rng.gen_range(0..KECCAK_LANE_SIZE)))
            .collect();
        let results = inputs
            .iter()
            .map(|&(v, _rot)| SpreadBits::try_from_u64(v, 64).unwrap().to_field())
            .collect::<Vec<_>>();
        let rot_results = inputs
            .iter()
            .map(|&(v, rot)| {
                SpreadBits::try_from_u64(v.rotate_right(rot as u32), 64).unwrap().to_field()
            })
            .collect::<Vec<_>>();

        // run the circuit honestly
        let circuit = TestSpreadDecompositionCircuit::<Fp> {
            inputs: inputs.clone(),
            _marker: PhantomData,
        };

        let prover = match MockProver::run(&circuit, vec![results, rot_results]) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        prover.assert_satisfied();
    }
}
