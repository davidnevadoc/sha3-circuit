#![allow(clippy::doc_lazy_continuation, clippy::doc_overindented_list_items)]
//! Module with helper functions for implementing rotations.
//!
//! Given the word size |W| = [`KECCAK_LANE_SIZE`] and the maximum lookup bit
//! size: [`MAX_BIT_LENGTH`],
//!
//! with the equality:
//!
//! [`KECCAK_LANE_SIZE`] = k * [`MAX_BIT_LENGTH`] + [`LAST_FIXED_LIMB_LENGTH`].
//!
//! We split a word in limbs of the following three groups:
//!
//! 1. full-size limbs (FL): fixed size [`MAX_BIT_LENGTH`]
//! 2. one leftover limb (LO): fixed size [`LAST_FIXED_LIMB_LENGTH`]
//! 3. two small limbs (SL1, SL2): variable sizes that sum to [`MAX_BIT_LENGTH`]
//!
//! For the rotation bit size: rot = q * [`MAX_BIT_LENGTH`] + r, 0 <= r <
//! [`MAX_BIT_LENGTH`],
//!
//! it corresponds to rotations of q full limbs and 1 small limb of size r.
//!
//! There are two cases regarding the relation between the rotation bits and
//! the word size:
//!
//! 1. rot = q * [`MAX_BIT_LENGTH`] + r <= |W| - |LO| = k * [`MAX_BIT_LENGTH`]
//!
//! In this case, the rotated chunk can be placed within the k full-size
//! limbs, so that one full-size limb could be split into SL1 and SL2 for |SL2|
//! = r. Therefore, the original word and rotated word could be represented
//! as:
//!
//! w =    | FLq+1 | ... | FLk | LO | SL1 | SL2 | FL1 | ... | FLq |
//! rotw = | SL2 | FL1 | ... | FLq | ... | FLk | LO | SL1 |     
//!     
//! 2. rot = q * [`MAX_BIT_LENGTH`] + r > |W| - |LO| = k * [`MAX_BIT_LENGTH`]
//!
//! In this case, the rotated chunk will cover all k full-size limbs. To
//! avoid splitting the LO limb and to keep the same shape of representation
//! (i.e only two small limbs SL1 and SL2 where |SL2| = r and |SL1| =
//! [`MAX_BIT_LENGTH`] - r), we use the following representation:
//!
//! w =    | SL1 - diff | SL2 + diff | FL1 | ... | FLk | LO |
//! rotw = | SL2 + diff | FL1 | ...  | FLk | LO  | SL1 - diff |
//!
//! where diff = [`MAX_BIT_LENGTH`] - LO. Note that the limbs SL1 - diff and SL2
//! + diff are well defined, i.e their sizes are in the range
//!   0..[`MAX_BIT_LENGTH`].
//! In fact, as r = |SL2| <= |LO| we have
//! |SL1 - diff| = [`MAX_BIT_LENGTH`] - r - ([`MAX_BIT_LENGTH`] - |LO|)
//!              = |LO| - r >= 0
//! |SL2 + diff| = |SL2| + [`MAX_BIT_LENGTH`] - |LO|
//!              = r + [`MAX_BIT_LENGTH`] - |LO| <= [`MAX_BIT_LENGTH`]
//!
//! Therefore, both cases can be witnessed in circuit as follows:
//!
//! | FL1 | ... | FLk | LO | SL1 | SL2 |
//!
//! where FL1, ..., FLk are the full-size limbs, LO is the leftover limb with
//! size [`LAST_FIXED_LIMB_LENGTH`], plus the two small limbs SL1
//! and SL2 where |SL2| = r and |SL1| = [`MAX_BIT_LENGTH`] - r.
//!
//! Finally, if the remainder r happens to be 0, we can just set |SL1| = FL - 1
//! and and |SL2| = 1, so that the limb size is always at least 1.
//!
//! # EXAMPLES
//!
//! MAX_BIT_LENGTH = 13, rot = 17
//! limbs sizes :         | 13 | 13 | 12 | 9  | 4  | 13 |
//! rotated limbs sizes : |  4 | 13 | 13 | 13 | 12 | 9  |
//!
//! MAX_BIT_LENGTH = 11, rot = 30
//! limbs sizes :         | 11 | 11 | 9  | 3  | 8  | 11  | 11 |
//! rotated limbs sizes : | 8  | 11 | 11 | 11 | 11 | 9   | 3  |
//!
//! MAX_BIT_LENGTH = 11, rot = 60, diff = 11 - 9 = 2
//! limbs sizes :         |  4 |  7 | 9  | 11 | 11 | 11  | 11 |
//! rotated limbs sizes : |  7 |  9 | 11 | 11 | 11 | 11  |  4 |

use ff::PrimeField;

use crate::{
    constants::KECCAK_LANE_SIZE,
    packed_chip::{LAST_FIXED_LIMB_LENGTH, MAX_BIT_LENGTH, NUM_FULL_LIMBS, NUM_LIMBS, TAG_COLS},
};

/// Computes the array of limb sizes (in big-endian) for 64 bits
/// lanes depending on the rotation bit length, and the number of full size
/// limbs that will be rotated to get the representation in circuit.
pub(super) fn limb_sizes(rot: usize) -> ([usize; NUM_LIMBS], usize) {
    // do mod KECCAK_LANE_SIZE to handle the case rot = 64
    // we do this because rot = 0 signals that we need no rotation
    let rot = rot % KECCAK_LANE_SIZE;

    // last two limb-sizes should add to MAX_BIT_LENGTH
    let mut a = rot % MAX_BIT_LENGTH;
    let mut b = MAX_BIT_LENGTH - a;

    let shift = rot / MAX_BIT_LENGTH;

    // initialize the result array
    let mut result = [MAX_BIT_LENGTH; NUM_LIMBS];

    // handle the 2nd case where rot > |W| - |LO| = k * MAX_BIT_LENGTH
    if shift > NUM_FULL_LIMBS {
        let diff = MAX_BIT_LENGTH - LAST_FIXED_LIMB_LENGTH;
        a += diff;
        b -= diff;
    }

    // handle the case where r = 0
    if a == 0 {
        a += 1;
        b -= 1;
    }

    // position the smaller limbs in the last positions
    result[NUM_LIMBS - 3] = LAST_FIXED_LIMB_LENGTH;
    result[NUM_LIMBS - 2] = b;
    result[NUM_LIMBS - 1] = a;

    // rotate to get the limb-sizes in the representation of the initial word:
    // w = | FLq+1 | ... | FLk | LO | SL1 | SL2 | FL1 | ...| FLq |
    result.rotate_left(shift);

    (result, shift)
}

/// Given a rotation bit length `rot`, computes the array of coefficients
/// corresponding to the limbs decomposition of the intial word or the rotated
/// word, depending on the `rotate` flag.     
/// The output array is re-ordered to match the representation used in circuit.
pub(super) fn get_dense_limb_coefficients<F: PrimeField>(
    rot: usize,
    rotate: bool,
) -> [F; NUM_LIMBS] {
    // get the needed limb sizes
    let (mut rotated_limb_sizes, q) = limb_sizes(rot);

    // find the shift of the limb_sizes array that gives the rotation
    // this can be explictly computed but it is cleaner to just take the
    // last limb sizes that sum to rot, which always exists.
    let array_rotation = if rotate {
        let mut shift = 0;
        let mut rotated_bits = 0;
        while rotated_bits != rot {
            rotated_bits += rotated_limb_sizes[NUM_LIMBS - 1 - shift];
            shift += 1
        }
        shift
    } else {
        0
    };

    // Rotate right the limb sizes to compute the rotated word coefficients.
    rotated_limb_sizes.rotate_right(array_rotation);

    // compute a running sum of the rotated limb sizes
    let mut sums = Vec::with_capacity(NUM_LIMBS);
    rotated_limb_sizes.iter().rfold(0, |sum, &x| {
        sums.push(sum);
        sum + x
    });
    sums.reverse();

    // compute the limb coefficients
    let coefficients = sums.iter().map(|&x| F::from(1 << x)).collect::<Vec<_>>();
    let mut coefficients: [F; NUM_LIMBS] = coefficients.try_into().unwrap();

    // rotate coefficients back to match the representation of the initial word
    coefficients.rotate_left(array_rotation);
    // get the representation used in circuit
    coefficients.rotate_right(q);

    coefficients
}

/// Same as [`get_dense_limb_coefficients`] for the spread limb coefficients.
/// This simply corresponds to cubing since we change
/// \sum limb_i 2^i --> \sum limb_i 8^i
pub(super) fn get_spread_limb_coefficients<F: PrimeField>(
    rot: usize,
    rotate: bool,
) -> [F; NUM_LIMBS] {
    get_dense_limb_coefficients::<F>(rot, rotate).map(|x| x * x * x)
}

/// Computes the limbs of a u64 word for the rotation bit length `rot`,
/// and reorders the limbs to match the representation used in circuit.
pub(super) fn lane_limbs(v: u64, rot: usize) -> [u64; NUM_LIMBS] {
    let (limb_sizes, q) = limb_sizes(rot);

    // tmp will be shifted to the right to compute the next limb
    let mut tmp = v;
    let mut limbs = Vec::with_capacity(NUM_LIMBS);
    for limb_size in limb_sizes.into_iter().rev() {
        let mask = (1 << limb_size) - 1;
        let limb = tmp & mask;
        limbs.push(limb);
        tmp >>= limb_size;
    }
    limbs.reverse();
    // match the representation to be used in-circuit
    limbs.rotate_right(q);
    limbs.try_into().unwrap()
}

/// Computes the variable limb sizes in a decomposed lane.
/// This contains two corresponding to the SL1, SL2
pub(super) fn limb_size_tags(rot: usize) -> [usize; TAG_COLS] {
    let (mut limb_sizes, q) = limb_sizes(rot);
    // get the representation used in circuit
    limb_sizes.rotate_right(q);
    // take the last 2 limb sizes which correspond to the small limbs
    [limb_sizes[NUM_LIMBS - 2], limb_sizes[NUM_LIMBS - 1]]
}
