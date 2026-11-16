//! The `BITS` table (BLUEPRINT §4.3; WP-12's `LvmBits`): per row a `K` word `w` and its 64 bit columns
//! `β_z` (`β_z² = β_z`, `w = Σ_z x^z·β_z`, i.e. `β_z` is bit `z` of the word), and the derived outputs, linear
//! forms in the bits written to the bus as cells: `shl k` = `w << k`, `shr k` = `w >> k`, `bit z`.
//! The rows' words (WOTS digest lanes and chain values, `σ'.idx`, the child's `n'`, the position answers,
//! the statement prefixes) and their order are fixed by the program `Q` (WP-11b/WP-12); this module fills
//! any list of words. Rows past the list are zero words (all constraints hold on them).
//!
//! [`BitsSpec::table`] (WP-15c) is the BITS class as WP-9's aux table (WP-12b `LvmBitsTab.BSpec.tab`): columns
//! `0` w, `1+z` β_z, `65` the word's read count, `66` its address `g^{wc x}` (fixed), `67+j` output `j`'s read
//! count, then the output addresses (fixed): with `sh > 0` one shared column `g^{oc 0 x}` at `67+|outs|` whose
//! `g^j` multiple is output `j`'s address for `j < sh` (lvm2 EVD2), then `g^{oc j x}` per output `j ≥ sh`;
//! constraints `w + Σ x^z β_z`, then `β_z² + β_z`; reads
//! only (the word when `rd`, then every output, whose value is the linear form `Σ coef_z β_z`); padding rows
//! `x ≥ n` repeat row 0 (word, bits, addresses), as further reads of row 0's cells with continuing counts.

use crate::lv::primitives::field::F64;

/// A derived output of a `BITS` row (`LvmBits.BOut`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BOut {
    Shl(u32),
    Shr(u32),
    Bit(u32),
    /// `Fld(z, m, d)`: the `m` bits of `w` from bit `z` on, placed at bit `d` (A20).
    Fld(u32, u32, u32),
}

impl BOut {
    /// The output's word as a function of the row's word (`BOut.word`).
    pub fn word(self, w: u64) -> u64 {
        match self {
            BOut::Shl(k) => w.wrapping_shl(k),
            BOut::Shr(k) => w.wrapping_shr(k),
            BOut::Bit(z) => (w >> z) & 1,
            BOut::Fld(z, m, d) => (w.wrapping_shr(z)).wrapping_shl(64 - m).wrapping_shr(64 - m - d),
        }
    }
    /// Where bit `z` of the word lands in the output, if it does (`BOut.hit`, `BOut.dst`).
    pub fn dst(self, z: u32) -> Option<u32> {
        match self {
            BOut::Shl(k) if z + k < 64 => Some(z + k),
            BOut::Shr(k) if z >= k => Some(z - k),
            BOut::Bit(b) if z == b => Some(0),
            BOut::Fld(z0, m, d) if z0 <= z && z < z0 + m && z - z0 + d < 64 => Some(z - z0 + d),
            _ => None,
        }
    }
    /// The coefficient of `β_z` in the output's linear form (`BOut.coef`): `x^{dst z}` when bit `z` lands.
    pub fn coef(self, z: u32) -> F64 {
        self.dst(z).map_or(F64::ZERO, |d| F64(1 << d))
    }
}

/// The committed columns of `BITS` with `2^log` rows: `w`, then `β_0 … β_63`.
pub struct BitsTable {
    pub w: Vec<F64>,
    pub beta: Vec<Vec<F64>>,
}

impl BitsTable {
    pub fn fill(log: usize, words: &[u64]) -> Self {
        let n = 1usize << log;
        assert!(words.len() <= n, "BITS: {} words > 2^{log} rows", words.len());
        let mut w = vec![F64::ZERO; n];
        let mut beta = vec![vec![F64::ZERO; n]; 64];
        for (i, &x) in words.iter().enumerate() {
            w[i] = F64(x);
            for z in 0..64 {
                beta[z][i] = F64((x >> z) & 1);
            }
        }
        Self { w, beta }
    }

    /// An output column as the bus sees it: `Σ_z coef_z·β_z` at every row.
    pub fn out(&self, o: BOut) -> Vec<F64> {
        (0..self.w.len()).map(|i| (0..64u32).fold(F64::ZERO, |acc, z| acc + o.coef(z) * self.beta[z as usize][i])).collect()
    }

    /// The two constraints of every row hold (`β² + β = 0`, `w + Σ x^z β_z = 0`), and every output's form is
    /// its word function: a self-check.
    pub fn check(&self, outs: &[BOut]) -> bool {
        let rows_ok = (0..self.w.len()).all(|i| {
            let s = (0..64).fold(F64::ZERO, |acc, z| acc + F64(1 << z) * self.beta[z][i]);
            (0..64).all(|z| (self.beta[z][i] * self.beta[z][i] + self.beta[z][i]).is_zero()) && (self.w[i] + s).is_zero()
        });
        rows_ok && outs.iter().all(|&o| self.out(o).iter().zip(&self.w).all(|(v, w)| v.0 == o.word(w.0)))
    }
}

/// A BITS class (WP-12b `BSpec`): `n` real rows of `2^tau`; row `x` reads the word of `K` cell `wc[x]` (when
/// `rd`; else the word is free, taken from that cell's value) and writes output `j` to `K` cell `oc[j][x]`;
/// `pl` places the committed columns (`w`, `β_0..63`, the word count, the output counts, in column order).
#[derive(Clone, Debug)]
pub struct BitsSpec {
    pub tau: usize,
    pub n: usize,
    pub rd: bool,
    pub outs: Vec<BOut>,
    pub wc: Vec<usize>,
    pub oc: Vec<Vec<usize>>,
    pub pl: Vec<(bool, usize)>,
    /// The first `sh` outputs share one address column (`BSpec.sh`; their cells are `oc[0][x] + j`).
    pub sh: usize,
}

impl BitsSpec {
    /// The first output-address column (`BSpec.ab`).
    pub fn ab(&self) -> usize {
        67 + self.outs.len()
    }
    /// The shared address columns (`BSpec.nA`: 0 or 1).
    pub fn n_a(&self) -> usize {
        if self.sh == 0 { 0 } else { 1 }
    }
    /// The width (`BSpec.width`): `67`, the output counts, the shared address column, the other addresses.
    pub fn width(&self) -> usize {
        self.ab() + self.n_a() + self.outs.len().saturating_sub(self.sh)
    }
    /// Output `j`'s address column and its `g`-power factor (`BSpec.oaddr`).
    pub fn oaddr(&self, j: usize) -> (usize, u32) {
        if j < self.sh { (self.ab(), j as u32) } else { (self.ab() + self.n_a() + (j - self.sh), 0) }
    }
    /// The real row whose cells row `x` reads (`BSpec.row`: padding rows repeat row 0).
    pub fn row(&self, x: usize) -> usize {
        if x < self.n { x } else { 0 }
    }
    /// Whether column `c` is committed (`BSpec.col`: `66` and the columns from `ab` are fixed).
    pub fn committed(&self, c: usize) -> bool {
        c != 66 && c < self.ab()
    }
    /// The `K` cells the table reads, in the order its count columns are filled: per row, the word (when
    /// `rd`), then every output.
    pub fn reads(&self) -> Vec<usize> {
        let mut v = Vec::with_capacity((1 << self.tau) * (self.outs.len() + 1));
        for x in 0..1usize << self.tau {
            let r = self.row(x);
            if self.rd {
                v.push(self.wc[r]);
            }
            v.extend(self.oc.iter().map(|o| o[r]));
        }
        v
    }

    /// The table: `words` = the `n` real rows' words, `cnt` = the counts of [`BitsSpec::reads`] in order,
    /// `g(e)` = `g^e`.
    pub fn table(&self, words: &[u64], cnt: &[F64], g: &dyn Fn(usize) -> F64) -> crate::lvm::m3::TableW {
        use crate::lv::leanvm_core::leaf::Coord;
        use crate::lvm::m3::{FlushW, TableW};
        assert!(words.len() == self.n && 1 <= self.n && self.n <= 1 << self.tau, "BITS: n real rows in 2^tau");
        assert!(self.wc.len() == self.n && self.oc.iter().all(|o| o.len() == self.n) && self.oc.len() == self.outs.len());
        assert!(self.sh <= self.outs.len(), "BITS: sh within the outputs (else the shared column is unfilled)");
        assert!((0..self.sh).all(|j| (0..self.n).all(|x| self.oc[j][x] == self.oc[0][x] + j)), "BITS: shared cells consecutive");
        let h = 1usize << self.tau;
        let w = self.width();
        let mut cols = vec![vec![F64::ZERO; h]; w];
        let mut k = 0;
        for x in 0..h {
            let r = self.row(x);
            let wd = words[r];
            cols[0][x] = F64(wd);
            for z in 0..64 {
                cols[1 + z][x] = F64((wd >> z) & 1);
            }
            cols[66][x] = g(self.wc[r]);
            if self.rd {
                cols[65][x] = cnt[k];
                k += 1;
            }
            for j in 0..self.outs.len() {
                cols[67 + j][x] = cnt[k];
                k += 1;
                let (a, f) = self.oaddr(j);
                if f == 0 {
                    cols[a][x] = g(self.oc[j][r]);
                }
            }
        }
        assert_eq!(k, cnt.len(), "BITS: a count per read");
        let mut cons = vec![[vec![(F64::ONE, vec![0])], (0..64).map(|z| (F64(1 << z), vec![1 + z])).collect()].concat()];
        cons.extend((0..64).map(|z| vec![(F64::ONE, vec![1 + z, 1 + z]), (F64::ONE, vec![1 + z])]));
        let sep = Coord::Const(crate::lvm::loopir::sep(crate::lvm::loopir::Ty::K));
        let mut reads: Vec<(usize, Coord, Coord)> = Vec::new(); // (count col, address, value)
        if self.rd {
            reads.push((65, Coord::Col(66), Coord::Col(0)));
        }
        for (j, o) in self.outs.iter().enumerate() {
            let v = Coord::Sum((0..64u32).filter_map(|z| o.dst(z).map(|d| Coord::GCol(1 + z as usize, d))).collect());
            let (a, f) = self.oaddr(j);
            reads.push((67 + j, if f == 0 { Coord::Col(a) } else { Coord::GCol(a, f) }, v));
        }
        let mut flushes = Vec::new();
        for (c, a, v) in &reads {
            flushes.push(FlushW { push: false, coords: vec![sep.clone(), a.clone(), Coord::Col(*c), v.clone()], count: Some(*c) });
            flushes.push(FlushW { push: true, coords: vec![sep.clone(), a.clone(), Coord::GCol(*c, 1), v.clone()], count: None });
        }
        let com: Vec<bool> = (0..w).map(|c| self.committed(c)).collect();
        let com_ix: Vec<usize> = (0..w).filter(|&c| com[c]).collect();
        assert_eq!(self.pl.len(), com_ix.len(), "BITS: a placement per committed column");
        let pre = com_ix.iter().zip(&self.pl).map(|(&c, &(r, o))| (c, r, o, true)).collect();
        TableW { tau: self.tau, cols, com, cons, flushes, pre, hdr: false }
    }
}
