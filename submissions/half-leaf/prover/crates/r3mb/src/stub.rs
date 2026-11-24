//! STUB tables (until CD's circuit generator and TY's typed memory `T` exist): four tables in roll #32's tableless
//! form, a `K` memory and an `E` memory, each a seed array and one read table ([`crate::typed_mb`]):
//!
//! | table | rows | columns (C = committed, F = fixed) | push / pull / count blocks |
//! |---|---|---|---|
//! | 0 `K` seeds, cells `g^x` | `2^10` | C val, C fin, F addr | 1 / 1 / 0 |
//! | 1 `E` seeds, cells `g^(4096 + 3x)` | `2^9` | C val₀, C val₁, C fin, F addr | 1 / 1 / 0 |
//! | 2 `K` reads | `2^10` | C addr, C val, C cnt | 1 / 1 / 1 |
//! | 3 `E` reads | `2^9` | C addr, C val₀, C val₁, C cnt | 1 / 1 / 1 |
//!
//! The push side has `3·2^10` leaves (depth 12, a quarter identity padding); the count side `3·2^9`. Committed:
//! 8,704 words, placed by [`crate::m3::place`] from `MB_LO`. Reads pick seeded cells pseudo-randomly (repeats
//! included, so counts climb past `g`), values are the cells', counts honest: push and pull are equal multisets.
//!
//! To swap real tables in: build `Vec<MbTab>` and every column's values (or an [`MbSpec`] for [`tables`]), place
//! the committed columns where the circuit puts them (`MbCol::Com { at }`), and hand
//! [`MbWitness::new`](crate::MbWitness::new) to the prover and the `Vec<MbTab>` to the verifier.

use crate::m3::place;
use crate::prove::MbWitness;
use crate::typed_mb::{MbRead, MbSeed, MbSpec, seed_addr, tables, tables_skipping};
use primitives::field::F64;
use r3core::layout::{MB_HI, MB_LO};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// The stub's seed arrays and read tables, from `seed`.
pub fn stub_spec(seed: u64) -> MbSpec {
    let mut rng = Rng(seed | 1);
    let mut seeds = Vec::new();
    for (limbs, base, stride, tau) in [(1usize, 0usize, 1usize, 10usize), (2, 4096, 3, 9)] {
        let vals = (0..limbs).map(|_| (0..1usize << tau).map(|_| F64(rng.next())).collect()).collect();
        seeds.push(MbSeed { limbs, base, stride, tau, vals });
    }
    let reads = seeds
        .iter()
        .map(|s: &MbSeed| {
            let addr_of = seed_addr(s.base, s.stride, s.tau);
            let n = 1usize << s.tau;
            // a quarter of the cells take most reads, so some cells are read many times and some never
            let cells: Vec<usize> =
                (0..n).map(|_| if rng.next() % 4 == 0 { (rng.next() as usize) % n } else { (rng.next() as usize) % (n / 4) }).collect();
            MbRead {
                limbs: s.limbs,
                tau: s.tau,
                addr: cells.iter().map(|&c| addr_of[c]).collect(),
                vals: (0..s.limbs).map(|l| cells.iter().map(|&c| s.vals[l][c]).collect()).collect(),
            }
        })
        .collect();
    MbSpec { seeds, reads }
}

/// The stub witness: [`stub_spec`]'s tables, placed in `MB_LO..MB_HI`.
pub fn stub_witness(seed: u64) -> MbWitness {
    let (mut tabs, values) = tables(&stub_spec(seed));
    place(&mut tabs, MB_LO, MB_HI);
    MbWitness::new(tabs, values)
}

/// Dev: the stub with read table `2`'s row 5 reading a wrong value (push ≠ pull as multisets).
pub fn stub_unbalanced(seed: u64) -> MbWitness {
    let mut w = stub_witness(seed);
    w.values[2][1][5].0 ^= 1;
    w
}

/// Dev: the stub with read table `3`'s (`E` reads) row 7 at count `0` (balanced, count product zero).
pub fn stub_zero_count(seed: u64) -> MbWitness {
    let (mut tabs, values) = tables_skipping(&stub_spec(seed), &[(1, 7)]);
    place(&mut tabs, MB_LO, MB_HI);
    MbWitness::new(tabs, values)
}
