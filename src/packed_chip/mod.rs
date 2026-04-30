//! Contains the packed arithmetic chip implementation for keccak

mod auxiliary_lc;
mod bootstrap;
mod bytes_to_spread;
mod decomposition;
mod keccakf_operations;
mod utils;

use std::marker::PhantomData;

use ff::PrimeField;
use keccakf_operations::KECCAK_ROWS_PER_PERMUTATION;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
};
use utils::{Bits, DenseBits};

use self::{
    keccakf_operations::types::AssignedKeccakState,
    utils::{AssignedDenseBits, AssignedSpreadBits, SpreadBits},
};
use crate::{
    constants::{
        KECCAK_ABSORB_BYTES, KECCAK_ABSORB_LANES, KECCAK_LANE_SIZE, KECCAK_NUM_ROUNDS,
        KECCAK_SQUEEZE_BYTES, KECCAK_WIDTH,
    },
    instructions::Keccackf1600Instructions,
};

// NOTE: It would be nice to have this as const generic. This seems currently
// not possible without carrying a lot of constants unless rust nightly is used.
//
// TODO: consider adding a feature with different MAX_BIT_LENGTH sizes
/// The log2 of the bound of the values assigned by the lookup. The value must
/// be at least 8 to support byte lookups.
const MAX_BIT_LENGTH: usize = 13;

/// The size of the remaining (fixed size) limb. Special care is needed if it is
/// also a max size limb
const LAST_FIXED_LIMB_LENGTH: usize = if KECCAK_LANE_SIZE.is_multiple_of(MAX_BIT_LENGTH) {
    MAX_BIT_LENGTH
} else {
    KECCAK_LANE_SIZE % MAX_BIT_LENGTH
};

/// Number of full limb lookups. If the remainder bit is a full limb use one
/// less
const NUM_FULL_LIMBS: usize = KECCAK_LANE_SIZE / MAX_BIT_LENGTH
    - 1
    - if KECCAK_LANE_SIZE.is_multiple_of(MAX_BIT_LENGTH) {
        1
    } else {
        0
    };

/// Number of lookup enabled columns. Defined by the number of full limbs and
/// the three extra limbs
const NUM_LIMBS: usize = NUM_FULL_LIMBS + 3;

/// The number of different TAGS looked up in a single row.
/// When decomposing a number in a single row it is always 2 corresponding to
/// the small limbs. The other limbs have a fixed limb size.
const TAG_COLS: usize = 2;

/// The base for spread representations.
const SPREAD_BASE_BITS: usize = 3;

/// Number of needed advice columns for [`PackedChip`].
pub const PACKED_ADVICE_COLS: usize = 4 + NUM_LIMBS;
/// Number of needed fixed columns for [`PackedChip`].
pub const PACKED_FIXED_COLS: usize = TAG_COLS + NUM_LIMBS;
/// Number of needed table columns for [`PackedChip`]
pub const PACKED_TABLE_COLS: usize = 3;

/// Struct containing the sub-config for the decomposition constraints
#[derive(Clone, Debug, Eq, PartialEq)]
struct DecompositionSubconfig {
    // selectors
    /// complex selector for rangechecking spread limbs
    q_assign_spread: Selector,

    /// selector for the lc constraint of decomposition
    q_dc: Selector,

    /// selector for rotating the current decomposed word in the next row
    q_rotate_next: Selector,

    // fixed columns
    /// tag columns for range checks
    tag_cols: [Column<Fixed>; TAG_COLS],

    /// constants for performing linear combinations
    /// in the [`DecompositionConfig::lookup_advice_cols`]
    dc_fixed_cols: [Column<Fixed>; NUM_LIMBS],

    // advice columns
    /// rangechecked enabled lookups
    dc_advice_cols: [Column<Advice>; NUM_LIMBS],
    /// advice columns for storing the result
    dc_result_col: Column<Advice>,

    // Lookup columns
    /// the lookup table
    t_tag: TableColumn,
    t_dense: TableColumn,
    t_spread: TableColumn,
}

impl DecompositionSubconfig {
    #[allow(clippy::too_many_arguments)]
    /// Given the needed columns creates the [`DecompositionSubconfig`]
    fn new(
        q_assign_spread: Selector,
        q_dc: Selector,
        q_rotate_next: Selector,
        tag_cols: [Column<Fixed>; TAG_COLS],
        dc_fixed_cols: [Column<Fixed>; NUM_LIMBS],
        dc_advice_cols: [Column<Advice>; NUM_LIMBS],
        dc_result_col: Column<Advice>,
        t_tag: TableColumn,
        t_dense: TableColumn,
        t_spread: TableColumn,
    ) -> Self {
        DecompositionSubconfig {
            q_assign_spread,
            q_dc,
            q_rotate_next,
            tag_cols,
            dc_fixed_cols,
            dc_advice_cols,
            dc_result_col,
            t_tag,
            t_dense,
            t_spread,
        }
    }

    /// Given the needed columns configures the [`DecompositionSubconfig`]
    fn configure<F: PrimeField>(&self, meta: &mut ConstraintSystem<F>) {
        // enable equalities
        meta.enable_equality(self.dc_result_col);

        // configure decomposition constraints
        self.configure_decomposition_gates(meta);
    }
}

/// Struct containing the sub-config for the bootstraping constraints
/// that imposes the constraint acc(omega X) = 2acc(X) + part(omega X)
#[derive(Clone, Debug, Eq, PartialEq)]
struct BootstrapSubconfig {
    // enables the bootstrap constraint
    q_bootstrap: Selector,
    /// Advice columns for the limb coefficient. This is the same
    /// as `res` column of [`DecompositionSubconfig`].
    part_col: Column<Advice>,
    /// bootstrapping accumulator column
    bootstrap_acc_col: Column<Advice>,
}

impl BootstrapSubconfig {
    /// Given the needed columns creates the [`BootstrapSubconfig`]
    fn new(
        q_bootstrap: Selector,
        part_col: Column<Advice>,
        bootstrap_acc_col: Column<Advice>,
    ) -> Self {
        BootstrapSubconfig {
            q_bootstrap,
            part_col,
            bootstrap_acc_col,
        }
    }

    /// Given the needed columns configures the [`BootstrapSubconfig`]
    fn configure<F: PrimeField>(&self, meta: &mut ConstraintSystem<F>) {
        // enable equalities
        meta.enable_equality(self.bootstrap_acc_col);

        // configure bootstraping constraints
        self.configure_bootstrap_gate(meta);
    }
}

/// Struct containing an auxiliary subconfig for perfoming simple linear
/// combinations for
///
/// - computing C values of theta step
/// - computing state after applying theta
/// - computing state after applying chi
/// - computing state after applying iota (only for the very last round)
///
/// It shares the bootstrap_acc_col with [`BootstrapSubconfig`] where the
/// results are computed
#[derive(Clone, Debug, Eq, PartialEq)]
struct LCSubconfig {
    /// enables the linear constraint computing cs
    q_c: Selector,
    /// enables the linear constraint computing theta
    q_theta: Selector,
    /// enables the linear constraint computing chi
    q_chi: Selector,
    /// enables the linear constraint for computing iota. This is
    /// the same constraint with q_theta
    q_iota: Selector,
    /// Advice columns. The last is shared with `bootstrap_acc_col` of
    /// [`BootstrapSubconfig`]. The other are fresh.
    advice: [Column<Advice>; 3],
}

impl LCSubconfig {
    /// Given the needed columns creates the [`LCSubconfig`]
    fn new(q_c: Selector, q_theta: Selector, q_chi: Selector, advice: [Column<Advice>; 3]) -> Self {
        // we don't add a new constraint for iota but we rather use the q_theta
        // constraint
        let q_iota = q_theta;
        LCSubconfig {
            q_c,
            q_theta,
            q_iota,
            q_chi,
            advice,
        }
    }

    /// Given the needed columns configures the [`LCSubconfig`]
    fn configure<F: PrimeField>(&self, meta: &mut ConstraintSystem<F>) {
        // enable equalities
        meta.enable_equality(self.advice[0]);
        meta.enable_equality(self.advice[1]);

        // configure bootstraping constraints
        self.configure_aux_lc_gates(meta);
    }
}

/// Struct containing an bytes-to-lane subconfig for assigning dense bytes
/// to spread lanes and converting in-cirucit between the two.
///
/// We use this to:
///
/// 1. absorb the input (dense -> spread)
/// 2. squeeze the output (spread -> dense)
///
/// It uses 4 rows to assign a lane/8 byte pair
#[derive(Clone, Debug, Eq, PartialEq)]
struct BytesToSpreadSubconfig {
    /// selector for enabling bytes to lane constraints,
    q_bytes_to_lane: Selector,
    /// lookup-enabled advice columns for assigning the limbs. We use 4 limbs
    /// regardless of [`MAX_BIT_LENGTH`]. This is enough for any meaningfull
    /// choice of [`MAX_BIT_LENGTH`] and will result in 4 rows per lane.
    limbs: [Column<Advice>; 4],
    /// advice column to hold the intermediate result, i.e. the recomposition
    /// of the first 4 out of 8 bytes to a (spread) u32
    intermediate: Column<Advice>,
    /// advice column to hold the recomposition result
    recomposition: Column<Advice>,
    /// the table columns
    t_tag: TableColumn,
    t_dense: TableColumn,
    t_spread: TableColumn,
}

impl BytesToSpreadSubconfig {
    /// Given the needed columns creates the [`LCSubconfig`]
    #[allow(clippy::too_many_arguments)]
    fn new(
        q_bytes_to_lane: Selector,
        limbs: [Column<Advice>; 4],
        intermediate: Column<Advice>,
        recomposition: Column<Advice>,
        t_tag: TableColumn,
        t_dense: TableColumn,
        t_spread: TableColumn,
    ) -> Self {
        BytesToSpreadSubconfig {
            q_bytes_to_lane,
            limbs,
            intermediate,
            recomposition,
            t_tag,
            t_dense,
            t_spread,
        }
    }

    #[allow(clippy::too_many_arguments)]
    /// Given the needed columns configures the [`BytesToSpreadSubconfig`]
    fn configure<F: PrimeField>(&self, meta: &mut ConstraintSystem<F>) {
        // enable equalities to copy the bytes
        (0..4).for_each(|i| meta.enable_equality(self.limbs[i]));
        meta.enable_equality(self.intermediate);
        meta.enable_equality(self.recomposition);

        // configure the subconfig
        self.configure_bytes_to_spread(meta);
    }
}

/// Struct containing the config for the packed lookup table chip
///
/// # NOTES
///
/// The layouter is not clever enough to only assign the
/// needed constants so we use an extra fixed column for constants.
///
/// Alternatively, when initialized, the chip can assign the constants
/// that it needs in one of its own fixed columns (must have equality support)
/// and keep them available in its state. This seems however unneeded since
/// most gadgets utilizing the chip will have such a column to share.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackedConfig {
    /// Column for holding constant values
    constant_column: Column<Fixed>,
    /// The decomposition subconfig
    decomposition_subconfig: DecompositionSubconfig,
    /// The bootstraping subconfig
    bootstrap_subconfig: BootstrapSubconfig,
    /// The auxiliary lc  subconfig
    lc_subconfig: LCSubconfig,
    /// The bytes_to_spread subconfig,
    bytes_to_spread_subconfig: BytesToSpreadSubconfig,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// The chip implementation with packed arithmetic
pub struct PackedChip<F: PrimeField> {
    config: PackedConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Chip<F> for PackedChip<F> {
    type Config = PackedConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> PackedChip<F> {
    /// Creates a chip given the config
    pub fn new(config: &PackedConfig) -> Self {
        // Assert field size is at least 192 bits
        assert!(F::NUM_BITS > 192);

        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    /// Configures [`PackedConfig`] using fresh columns
    pub fn from_scratch(meta: &mut ConstraintSystem<F>) -> PackedConfig {
        let constant_column = meta.fixed_column();
        // simpy create the needed columns and call configure
        let advice_columns =
            (0..PACKED_ADVICE_COLS).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed_columns = (0..PACKED_FIXED_COLS).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        PackedChip::configure(
            meta,
            constant_column,
            advice_columns.try_into().unwrap(),
            fixed_columns.try_into().unwrap(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    /// Given the needed columns creates the [`PackedConfig`]
    fn configure_from_subconfigs(
        meta: &mut ConstraintSystem<F>,
        constant_column: Column<Fixed>,
        decomposition_subconfig: DecompositionSubconfig,
        bootstrap_subconfig: BootstrapSubconfig,
        lc_subconfig: LCSubconfig,
        bytes_to_spread_subconfig: BytesToSpreadSubconfig,
    ) -> PackedConfig {
        decomposition_subconfig.configure(meta);
        bootstrap_subconfig.configure(meta);
        lc_subconfig.configure(meta);
        bytes_to_spread_subconfig.configure(meta);

        PackedConfig {
            constant_column,
            decomposition_subconfig,
            bootstrap_subconfig,
            lc_subconfig,
            bytes_to_spread_subconfig,
        }
    }

    /// Given the needed columns, it creates and configures the [`PackedConfig`]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        constant_column: Column<Fixed>,
        advice_columns: [Column<Advice>; PACKED_ADVICE_COLS],
        fixed_columns: [Column<Fixed>; PACKED_FIXED_COLS],
    ) -> PackedConfig {
        meta.enable_constant(constant_column);

        // Freshly generating the table columns, as they a priori cannot be shared by
        // the other chips.
        let mut table_columns = Vec::new();
        for _ in 0..PACKED_TABLE_COLS {
            table_columns.push(meta.lookup_table_column());
        }
        let table_columns: [TableColumn; PACKED_TABLE_COLS] = table_columns.try_into().unwrap();

        // 1. configure the decomposition subconfig

        // use the first complex selectors for the lookup
        let q_assign_spread = meta.complex_selector();

        // the same selector can be used. We use different selectors in test to
        // allow negative testing
        #[cfg(not(test))]
        let q_dc = q_assign_spread;
        #[cfg(test)]
        // use the first complex selectors for the lookup
        let q_dc = meta.selector();

        // rotate the current limbs in the next row
        let q_rotate_next = meta.selector();

        // advice coluns. The layout is as follows (X for unused):
        // | res | X |  X  |  X  |  limb1  | ... |   limbk  |
        let result_col = advice_columns[0];
        let dc_advice_cols = advice_columns[4..4 + NUM_LIMBS].to_vec();

        // fixed coluns. the layout looks like:
        // | tag0 | tag1 | --res_coef-- |
        let tag_cols = fixed_columns[0..TAG_COLS].to_vec();
        let dc_fixed_cols = fixed_columns[TAG_COLS..].to_vec();
        let (t_tag, t_dense, t_spread) = (table_columns[0], table_columns[1], table_columns[2]);
        let decomposition_subconfig = DecompositionSubconfig::new(
            q_assign_spread,
            q_dc,
            q_rotate_next,
            tag_cols.try_into().unwrap(),
            dc_fixed_cols.try_into().unwrap(),
            dc_advice_cols.try_into().unwrap(),
            result_col,
            t_tag,
            t_dense,
            t_spread,
        );

        // 2. configure the bootstrap subconfig
        // fresh selector
        let q_bootstrap = meta.selector();

        // advice coluns. The layout looks like (X for unused):
        // | part | X | X | acc |  X  | ... |   X  |
        let part_col = advice_columns[0];
        let bootstrap_acc_col = advice_columns[3];

        let bootstrap_subconfig = BootstrapSubconfig::new(q_bootstrap, part_col, bootstrap_acc_col);

        // 3. configure the lc subconfig
        let q_c = meta.selector();
        let q_theta = meta.selector();
        let q_chi = meta.selector();

        // advice coluns. The layout looks like (X for unused):
        // | X |  a1  | a2 |  acc  |  X  | ... |   X  |
        let advice = advice_columns[1..4].to_vec();

        let lc_subconfig = LCSubconfig::new(q_c, q_theta, q_chi, advice.try_into().unwrap());

        // 4. configure the bytes_to_spread_subconfig
        let q_bytes_to_lane = meta.complex_selector();

        // use the first four lookup enabled columns and two extra advice cols
        // the layout looks like this:
        // | res | intermediate | limb3 | ... | limb0 |
        let limbs = advice_columns[4..8].to_vec().try_into().unwrap();

        // use the first two advice columns for the result and intermediate
        let recomposition = advice_columns[0];
        let intermediate = advice_columns[1];

        let bytes_to_spread_subconfig = BytesToSpreadSubconfig::new(
            q_bytes_to_lane,
            limbs,
            intermediate,
            recomposition,
            t_tag,
            t_dense,
            t_spread,
        );

        PackedChip::configure_from_subconfigs(
            meta,
            constant_column,
            decomposition_subconfig,
            bootstrap_subconfig,
            lc_subconfig,
            bytes_to_spread_subconfig,
        )
    }

    /// Loads the lookup table.
    ///
    /// The lookup table is of the form ():
    ///
    /// |MAX_BOUND | DENSE   | SPREAD
    /// |----------|---------|------------
    /// |0         | 0       | 0    
    /// |1         | 0b0     | 0b000
    /// |1         | 0b1     | 0b001
    /// |2         | 0b00    | 0b000
    /// |2         | 0b01    | 0b001
    /// |2         | 0b10    | 0b001_000
    /// |2         | 0b11    | 0b001_001
    ///
    /// ...
    /// For the case of MAX_BIT_LENGTH, we do **not** repeat the previous
    /// values. Instead, we do the lookup while ignoring the tag. An unused
    /// tag still needs to be set for these rows to prevent one of the other
    /// (tag, cols) pairs to match.
    pub fn load_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let decomposition_config = self.config.decomposition_subconfig.clone();
        layouter.assign_table(
            // we assign the special triple (0,0,0) to be able to disable the lookup
            || "spread table",
            |mut table| {
                let mut offset = 0;
                table.assign_cell(
                    || "t_tag",
                    decomposition_config.t_tag,
                    offset,
                    || Value::known(F::ZERO),
                )?;
                table.assign_cell(
                    || "t_dense",
                    decomposition_config.t_dense,
                    offset,
                    || Value::known(F::ZERO),
                )?;
                table.assign_cell(
                    || "t_spread",
                    decomposition_config.t_spread,
                    offset,
                    || Value::known(F::ZERO),
                )?;
                offset += 1;
                // assign all but full length limbs
                for bit_len in 1..=MAX_BIT_LENGTH - 1 {
                    let tag = Value::known(F::from(bit_len as u64));
                    for dense in 0..(1u64 << bit_len) {
                        // never panics
                        let dense_bits: DenseBits =
                            Bits::try_from_u64(dense, bit_len).unwrap().into();
                        let spread_bits = dense_bits.spread();
                        table.assign_cell(
                            || "t_tag",
                            decomposition_config.t_tag,
                            offset,
                            || tag,
                        )?;
                        table.assign_cell(
                            || "t_dense",
                            decomposition_config.t_dense,
                            offset,
                            || Value::known(dense_bits.to_field::<F>()),
                        )?;
                        table.assign_cell(
                            || "t_spread",
                            decomposition_config.t_spread,
                            offset,
                            || Value::known(spread_bits.to_field::<F>()),
                        )?;
                        offset += 1;
                    }
                }
                // assign the remaining values
                for dense in (1u64 << (MAX_BIT_LENGTH - 1))..(1u64 << MAX_BIT_LENGTH) {
                    // does never panic
                    let dense_bits: DenseBits =
                        Bits::try_from_u64(dense, MAX_BIT_LENGTH).unwrap().into();
                    let spread_bits = dense_bits.spread();
                    // use a tag that is not used in previous cases
                    // this prevents looking this part when searching for smaller bit lengths
                    table.assign_cell(
                        || "t_tag",
                        decomposition_config.t_tag,
                        offset,
                        || Value::known(F::from(MAX_BIT_LENGTH as u64)),
                    )?;
                    table.assign_cell(
                        || "t_dense",
                        decomposition_config.t_dense,
                        offset,
                        || Value::known(dense_bits.to_field::<F>()),
                    )?;
                    table.assign_cell(
                        || "t_spread",
                        decomposition_config.t_spread,
                        offset,
                        || Value::known(spread_bits.to_field::<F>()),
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}

/// Struct represenging an assigned block of absorbed bytes. It consists of
///
/// - the 136 absorbed bytes in dense form
/// - the 17 absorbed lane in spread form
/// - an assigned value of zero that can be copied to fill up the block
#[derive(Clone, Debug)]
pub struct AbsorbedBlock<F: PrimeField> {
    dense_bytes: [AssignedDenseBits<F>; KECCAK_ABSORB_BYTES],
    spread_lanes: [AssignedSpreadBits<F>; KECCAK_ABSORB_LANES],
    assigned_zero: AssignedSpreadBits<F>,
}

impl<F: PrimeField> From<AbsorbedBlock<F>> for Vec<AssignedDenseBits<F>> {
    fn from(block: AbsorbedBlock<F>) -> Self {
        block.dense_bytes.into()
    }
}

// implement the keccak-f instruction
impl<F: PrimeField> Keccackf1600Instructions<F> for PackedChip<F> {
    type State = AssignedKeccakState<F>;

    type Lane = AssignedSpreadBits<F>;

    type AbsorbedBlock = AbsorbedBlock<F>;

    type Digest = [Self::AssignedByte; KECCAK_SQUEEZE_BYTES];

    type UnassignedByte = DenseBits;

    type AssignedByte = AssignedDenseBits<F>;

    fn min_k(len: usize) -> u32 {
        let num_absorbed_blocks = len / KECCAK_ABSORB_BYTES + 1;

        // the number of rows is
        // - 4 rows per absorbed lane to absorb the input lanes
        //   (4*17*num_absorbed_blocks)
        // - KECCAK_ROWS_PER_PERMUTATION for each permutation
        //   (KECCAK_ROWS_PER_PERMUTATION * num_absorbed_blocks)
        // - 4 rows per squeezed lane (16)
        let nr_rows_log_f = num_absorbed_blocks
            * (KECCAK_ROWS_PER_PERMUTATION + 4 * KECCAK_ABSORB_LANES)
            + KECCAK_SQUEEZE_BYTES / 4;

        // the number of rows needed for the lookup table
        let nr_rows_log_table = (1 << (MAX_BIT_LENGTH + 1)) as u32;
        let nr_rows = nr_rows_log_table.max(nr_rows_log_f as u32);

        // we remove some rows (more than enough) for zero knowledge
        32 - (nr_rows - 10).leading_zeros()
    }

    fn assign_message_block(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[Value<Self::UnassignedByte>; KECCAK_ABSORB_BYTES],
    ) -> Result<Self::AbsorbedBlock, Error> {
        // group 8 bytes to a spread lane
        let spread_lanes = bytes
            .chunks(8)
            .map(|bytes| {
                bytes.iter().rev().fold(Value::known(0u64), |acc, v| {
                    acc.zip(v.clone()).map(|(acc, v)| acc * 256 + v.to_lane())
                })
            })
            .map(|lane| lane.map(|lane| SpreadBits::try_from_u64(lane, 64).unwrap()))
            .collect::<Vec<_>>();

        // convert bytes to chunks of dense bytes
        let dense_bytes: Vec<[_; 8]> = bytes
            .chunks(8)
            .map(|bytes| bytes.to_vec().try_into().unwrap())
            .collect::<Vec<_>>();

        // sanity check
        debug_assert_eq!(spread_lanes.len(), dense_bytes.len());

        // Assign the dense bytes-spread lane pairs.
        // Note that this guarantees
        // 1. the dense bytes are indeed bytes
        // 2. the spread lane correspond to the sread value of the combined bytes
        let (assigned_block, assigned_zero) = layouter.assign_region(
            || "assign message block to be absorbed",
            |mut region| {
                let assigned_block = spread_lanes
                    .iter()
                    .zip(dense_bytes.iter())
                    .enumerate()
                    .map(|(i, (lane, bytes))| {
                        // assign bytes/lanes. Returns the assigned values.
                        self.assign_bytes_and_spread(
                            &mut region,
                            // need 4 rows per lane
                            4 * i,
                            bytes,
                            lane,
                        )
                    })
                    .collect::<Result<Vec<_>, Error>>()?;

                // we assign a fixed value 0 on an unused cell outside the permutation region
                // we do this in the intermediate column, first row of bytes_to_spread_subconfig
                let spread_zero = SpreadBits::try_from_u64(0, 64).unwrap();
                let assigned_zero = region.assign_advice_from_constant(
                    || "assign zero spread lane",
                    self.config().bytes_to_spread_subconfig.intermediate,
                    0,
                    spread_zero,
                )?;
                Ok((assigned_block, assigned_zero))
            },
        )?;

        let spread_lanes = assigned_block.iter().map(|v| v.0.clone()).collect::<Vec<_>>();
        let dense_bytes = assigned_block.iter().flat_map(|v| v.1.clone()).collect::<Vec<_>>();

        // convert to an assigned block and return
        Ok(AbsorbedBlock {
            dense_bytes: dense_bytes.try_into().unwrap(),
            spread_lanes: spread_lanes.try_into().unwrap(),
            assigned_zero,
        })
    }

    fn initialize(&self, _layouter: &mut impl Layouter<F>) -> Result<Self::State, Error> {
        // We do not implement it since this introduces unneeded overhead. One should
        // always use `initialize_and_absorb`
        unimplemented!()
    }

    fn initialize_and_absorb(
        &self,
        _layouter: &mut impl Layouter<F>,
        block: &Self::AbsorbedBlock,
    ) -> Result<Self::State, Error> {
        let assigned_zero = &block.assigned_zero;

        // initialize the state with zeros
        let mut inner =
            [[0u64; KECCAK_WIDTH]; KECCAK_WIDTH].map(|lanes| lanes.map(|_| assigned_zero.clone()));

        // replace the (i,j)-th element with the  (i + 5j)-th assigned lane
        block.spread_lanes.iter().enumerate().for_each(|(k, m)| {
            inner[k % 5][k / 5] = m.clone();
        });

        Ok(AssignedKeccakState { inner })
    }

    fn absorb(
        &self,
        _layouter: &mut impl Layouter<F>,
        _state: &Self::State,
        _ms: &Self::AbsorbedBlock,
    ) -> Result<Self::State, Error> {
        // we always perform the absorbing together with the permutation or during
        // initialization for efficiency reasons
        unimplemented!()
    }

    fn keccakf(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<Self::State, Error> {
        layouter.assign_region(
            || "keccakf permutation region",
            |mut region| {
                // apply the rounds
                (0..KECCAK_NUM_ROUNDS).try_fold(state.clone(), |old_state, round| {
                    self.keccakf_round(&mut region, round, &old_state, None)
                })
            },
        )
    }

    fn keccakf_and_absorb(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
        ms: Option<&Self::AbsorbedBlock>,
    ) -> Result<Self::State, Error> {
        layouter.assign_region(
            || "keccakf permutation with absorb region",
            |mut region| {
                // apply all rounds except the last
                let state = (0..KECCAK_NUM_ROUNDS - 1)
                    .try_fold(state.clone(), |old_state, round| {
                        self.keccakf_round(&mut region, round, &old_state, None)
                    })?;

                // apply the last round and absorb
                let ms = ms.map(|block| &block.spread_lanes);
                self.keccakf_round(&mut region, KECCAK_NUM_ROUNDS - 1, &state, ms)
            },
        )
    }

    fn squeeze(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<Self::Digest, Error> {
        let result = layouter.assign_region(
            || "keccakf squeeze region",
            |mut region| {
                // 4 lanes as output
                (0..4)
                    .map(|i| {
                        let lane = state.inner[i][0].clone();
                        self.convert_spread_lane_to_bytes(&mut region, 4 * i, &lane)
                    })
                    .collect::<Result<Vec<_>, _>>()
            },
        )?;

        // convert to an array of AssignedDenseBits and return
        let digest = result.iter().flat_map(|v| v.to_vec()).collect::<Vec<_>>().try_into().unwrap();

        Ok(digest)
    }
}
