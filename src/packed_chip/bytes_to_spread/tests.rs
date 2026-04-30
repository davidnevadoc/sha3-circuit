use std::marker::PhantomData;

use ff::PrimeField;
use midnight_curves::Fq as Fp;
use midnight_proofs::{
    circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::packed_chip::{utils::SpreadBits, PackedChip, PackedConfig, MAX_BIT_LENGTH};

// converts spread lanes to dense bytes
#[derive(Debug)]
struct TestLaneToBytesCircuit<F: PrimeField> {
    // input consists of a u64 lane
    inputs: Vec<u64>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for TestLaneToBytesCircuit<F> {
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
        let instance_col = meta.instance_column();
        meta.enable_equality(instance_col);
        (packed_config, instance_col)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // create chip
        let packed_chip = PackedChip::<F>::new(&config.0);
        packed_chip.load_table(&mut layouter)?;

        // assign the spread lanes bytes (unchecked)
        let assigned_lanes = layouter.assign_region(
            || "assign lanes unchecked",
            |mut region| {
                self.inputs
                    .iter()
                    .enumerate()
                    .map(|(i, &lane)| {
                        let spread_lane = SpreadBits::try_from_u64(lane, 64).unwrap();
                        region.assign_advice(
                            || "assign lane",
                            packed_chip.config().bytes_to_spread_subconfig.recomposition,
                            i,
                            || Value::known(spread_lane.clone()),
                        )
                    })
                    .collect::<Result<Vec<_>, Error>>()
            },
        )?;

        // convert to bytes
        let results = layouter.assign_region(
            || "bytes to lane region",
            |mut region| {
                assigned_lanes
                    .iter()
                    .enumerate()
                    .map(|(offset, lane)| {
                        packed_chip.convert_spread_lane_to_bytes(
                            &mut region,
                            // four rows per assignment
                            4 * offset,
                            lane,
                        )
                    })
                    .collect::<Result<Vec<_>, Error>>()
            },
        )?;

        // "flatten" the bytes to assign them to a single instance column
        results
            .iter()
            .flat_map(|v| v.to_vec())
            .enumerate()
            .try_for_each(|(i, byte)| layouter.constrain_instance(byte.cell(), config.1, i))?;

        Ok(())
    }
}

#[test]
fn test_spread_lane_to_bytes() {
    let k = MAX_BIT_LENGTH as u32 + 1;

    let number_of_inputs = 10;

    // test a few random inputs
    let mut rng = ChaCha8Rng::from_entropy();
    let inputs: Vec<u64> = (0..number_of_inputs).map(|_| rng.next_u64()).collect::<Vec<_>>();

    // run the circuit honestly
    let circuit = TestLaneToBytesCircuit::<Fp> {
        inputs: inputs.clone(),
        _marker: PhantomData,
    };

    let expected = inputs
        .clone()
        .iter()
        .flat_map(|lane| lane.to_le_bytes().map(|u| u as u64))
        .map(Fp::from)
        .collect::<Vec<_>>();

    let prover = match MockProver::run(&circuit, vec![expected]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };

    prover.assert_satisfied();
}
