//! FORMAT6 v2.4 §6.4b, prover side: the witness's committed columns on the stack, and the mini-bus proof with its
//! three stack claims (§6.4's claims 50–52, in order: push, pull, count).

use std::collections::HashMap;

use crate::m3::{TableW, prove_lin};
use crate::tables::{MbCol, MbTab, check_static, cpoly};
use crate::transcript::ProverState;
use crate::{MB_MU, MB_OFF};
use primitives::field::{F64, F128};
use primitives::multilinear::eq_table;
use r3core::claim::PClaim;
use r3core::layout::{MB_HI, MB_LO, STACK_LOG};

/// The mini-bus's tables and every column's values (`values[t][c]`, `2^τ` words; a fixed column's equal its
/// description's).
#[derive(Clone)]
pub struct MbWitness {
    pub tabs: Vec<MbTab>,
    pub values: Vec<Vec<Vec<F64>>>,
}

impl MbWitness {
    /// Checks the tables' static conditions ([`check_static`]: tableless form, placement, depth 12) and the shapes.
    pub fn new(tabs: Vec<MbTab>, values: Vec<Vec<Vec<F64>>>) -> Self {
        check_static(&tabs);
        assert_eq!(tabs.len(), values.len(), "one value list per table");
        for (t, v) in tabs.iter().zip(&values) {
            assert_eq!(v.len(), t.width(), "one value column per column");
            for (c, col) in t.cols.iter().zip(v) {
                assert_eq!(col.len(), 1 << t.tau);
                if let MbCol::Fix(f) = c {
                    assert_eq!(f, col, "a fixed column's values are its description's");
                }
            }
        }
        MbWitness { tabs, values }
    }

    /// Write the committed columns inside `MB_LO..MB_HI` (r3mb's own: the counts, the finalizes, the stub's) into
    /// the stack (`2^25` words); a column elsewhere (R7: `T` or `STREAM` words, the typed witness's) must already
    /// hold its values. Aliased columns must agree.
    pub fn write(&self, stack: &mut [F64]) {
        assert_eq!(stack.len(), 1 << STACK_LOG);
        let mut written: HashMap<usize, usize> = HashMap::new();
        for (t, v) in self.tabs.iter().zip(&self.values) {
            for (c, col) in t.cols.iter().zip(v) {
                if let MbCol::Com { at } = *c {
                    if !(at >= MB_LO && at + col.len() <= MB_HI) {
                        assert_eq!(&stack[at..at + col.len()], col.as_slice(), "a column outside MB_LO..MB_HI is on the stack");
                        continue;
                    }
                    if written.insert(at, col.len()).is_some() {
                        assert_eq!(&stack[at..at + col.len()], col.as_slice(), "an aliased column agrees");
                    }
                    stack[at..at + col.len()].copy_from_slice(col);
                }
            }
        }
    }

    /// Prover self-check (dev): push and pull are equal multisets and every count is nonzero. The proof needs the
    /// first (the vendored GKR asserts the two roots equal); the verifier rejects a zero count.
    pub fn balanced(&self) -> (bool, bool) {
        let mut bag: HashMap<Vec<u64>, i64> = HashMap::new();
        let mut nonzero = true;
        for (t, v) in self.tabs.iter().zip(&self.values) {
            let tw = TableW::of(t, |c| v[c].clone());
            for f in &tw.flushes {
                for x in 0..1usize << t.tau {
                    let tuple: Vec<u64> = f
                        .coords
                        .iter()
                        .map(|co| cpoly(co).iter().fold(F64::ZERO, |a, (k, col)| a + *k * col.map_or(F64::ONE, |c| v[c][x])).0)
                        .collect();
                    *bag.entry(tuple).or_insert(0) += if f.push { 1 } else { -1 };
                }
                if let Some(c) = f.count {
                    nonzero &= v[c].iter().all(|w| w.0 != 0);
                }
            }
        }
        (bag.values().all(|&n| n == 0), nonzero)
    }
}

/// The aligned stack block `(off, μ)` the claims' dense weights sit on: the mini-bus block `MB_OFF, MB_MU` when
/// every committed column lies in it (the stub), else the smallest aligned block holding every column (R7: real
/// tables with `T`/`STREAM` columns). The weight is the same polynomial either way (Lean `mbClaimsG`'s parts).
pub fn claim_block(tabs: &[MbTab]) -> (usize, usize) {
    let spans: Vec<(usize, usize)> = tabs
        .iter()
        .flat_map(|t| t.cols.iter().filter_map(move |c| if let MbCol::Com { at } = c { Some((*at, at + (1 << t.tau))) } else { None }))
        .collect();
    if spans.iter().all(|&(a, b)| a >= MB_LO && b <= MB_HI) {
        return (MB_OFF, MB_MU);
    }
    let lo = spans.iter().map(|s| s.0).min().expect("a committed column");
    let hi = spans.iter().map(|s| s.1).max().unwrap() - 1;
    let mut mu = 0;
    while lo >> mu != hi >> mu {
        mu += 1;
    }
    (lo >> mu, mu)
}

/// What §6.4b leaves: claims 50–52 (push, pull, count; `PClaim`s on the mini-bus block of the stack), and for the
/// dev checks the GKR point `ζ`, the fingerprint and the trees' leaf values `Ṽ_s(ζ)`.
pub struct MbOut {
    pub claims: Vec<PClaim>,
    pub point: Vec<F128>,
    pub alphas: Vec<F128>,
    pub beta: F128,
    pub values: [F128; 3],
}

/// **FORMAT6 §6.4b** on `ps` (a v6 state whose buffer is empty, so the fingerprint's ground query is 40 bytes):
/// `G(16), D(4)` → `α₀ … α₃, β`; `E(2)` roots `shared, count`; 6 steps of `G(2)` → `λ_k`, `2k × R(4, 3)` eq mode,
/// `E(4) × 3` children, `G(2), D(1)` → `y_k` (step 5: `G(3), D(1)`). The committed columns are read from `stack`
/// (where [`MbWitness::write`] put them). Returns the three claims, each one stacked claim
/// `Σ_{(t,c)} coef·col~_{t,c}(ζ[..τ_t]) = value` placed on the mini-bus block (FORMAT6 §6.5 placement).
pub fn prove_minibus(ps: &mut ProverState, w: &MbWitness, stack: &[F64]) -> MbOut {
    assert_eq!(stack.len(), 1 << STACK_LOG);
    let tables: Vec<TableW> = w
        .tabs
        .iter()
        .zip(&w.values)
        .map(|(t, v)| {
            TableW::of(t, |c| {
                let MbCol::Com { at } = t.cols[c] else { unreachable!() };
                let col = stack[at..at + (1 << t.tau)].to_vec();
                assert_eq!(col, v[c], "the stack holds the witness's committed columns (MbWitness::write)");
                col
            })
        })
        .collect();
    let lin = crate::stage!("Mini-bus", || prove_lin(ps, &tables));
    assert_eq!(lin.point.len(), crate::MINI_DEPTH);
    let labels = ["50 mb push", "51 mb pull", "52 mb count"];
    let (off, mu) = claim_block(&w.tabs);
    let claims = lin
        .claims
        .iter()
        .zip(labels)
        .map(|(cl, label)| {
            // (offset inside the block, τ, coefficient)
            let terms: Vec<(usize, usize, F128)> = cl
                .terms
                .iter()
                .map(|&(t, c, k)| {
                    let MbCol::Com { at } = w.tabs[t].cols[c] else { unreachable!() };
                    (at - (off << mu), w.tabs[t].tau, k)
                })
                .collect();
            let zeta = lin.point.clone();
            PClaim::dense(label, off, mu, cl.value, move |scale, out: &mut [F128]| {
                for &(off, tau, k) in &terms {
                    let eq = eq_table(&zeta[..tau]);
                    let s = scale * k;
                    for (o, e) in out[off..off + (1 << tau)].iter_mut().zip(eq) {
                        *o += s * e;
                    }
                }
            })
        })
        .collect();
    MbOut { claims, point: lin.point, alphas: lin.alphas, beta: lin.beta, values: lin.values }
}
