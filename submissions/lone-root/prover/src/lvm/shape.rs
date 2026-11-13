//! SH2-Z (roll 7, CR-DES §1; the Lean `LvmShape`): the small shape of `C_main`.
//!
//! A `P20` step with `n ≤ 2^18` holds `C_main` as the logical `2^23`-word table of `layout::P20S`
//! ([`Layout::shape`] with `small`): `D_l`'s rows `< 2^18` at `l·2^18`, the big layout's blocks from `KS` up moved
//! down by `3·2^20`. It commits the `2^24`-word table whose word `2w` is logical word `w` and whose odd words are
//! zero (`whir::commit_even`, the same commitment as `whir::commit` of that table, CR-P0 P1).
//!
//! Every phase before the opening is the big layout's: the claims carry the big layout's points and values (`D`'s
//! rows `≥ 2^18` are `z*_l = Keccak-f(0)[l]`, what the chain gives a dead row). [`relocate`] then puts each claim on
//! the physical stack, as `LvmShape.onStackZ` does: a word's weight moves from big word `a` to physical word
//! `2·σ(a)`, the odd words get none, and the value loses the weight's mass on `D`'s rows `≥ 2^18` times `z*`.
//! The claim's weight has the same values on the cube as `onStackZ`'s, so the opening is the verifier's.

use crate::lv::primitives::field::{F64, F192};
use crate::lvm::link::Claim;
use crate::lvm::m3::TableW;
use crate::lvm::params::LANES;
use crate::lvm::tables::{Layout, SMALL_SHIFT};

/// `z* = Keccak-f(0)[0..4)`: `D`'s value on every row `≥ n`.
pub fn z_star() -> [u64; 4] {
    let mut z = [0u64; LANES];
    crate::lv::primitives::hash::keccak_f(&mut z);
    [z[0], z[1], z[2], z[3]]
}

/// The buffer offset of the big-layout words `o .. o + len`, if they are contiguous there: the identity in the big
/// shape; in the small one `None` when they meet `D`'s rows `≥ 2^d_log` (not held: `z*`).
pub fn buf_range(lay: &Layout, o: usize, len: usize) -> Option<usize> {
    if !lay.small {
        return Some(o);
    }
    let big_d = 4usize << lay.log_n;
    if o < big_d {
        let (l, i) = (o >> lay.log_n, o & ((1 << lay.log_n) - 1));
        (i + len <= 1 << lay.d_log).then(|| lay.d(l) + i)
    } else {
        assert!(o + len - SMALL_SHIFT <= 1 << lay.nu_main, "a big word above the small table's room");
        Some(o - SMALL_SHIFT)
    }
}

/// The big-layout words `o .. o + len` of the buffer `buf` (`z*_l` on `D_l`'s rows `≥ 2^d_log`).
pub fn read_big(lay: &Layout, buf: &[F64], o: usize, len: usize) -> Vec<F64> {
    if let Some(b) = buf_range(lay, o, len) {
        return buf[b..b + len].to_vec();
    }
    let z = z_star();
    (o..o + len)
        .map(|a| match buf_range(lay, a, 1) {
            Some(b) => buf[b],
            None => F64(z[a >> lay.log_n]),
        })
        .collect()
}

/// The tables' `C_main` pre-placements (the blob's, big-layout offsets) as buffer offsets.
pub fn localize(lay: &Layout, tables: &mut [TableW]) {
    if !lay.small {
        return;
    }
    for t in tables {
        let len = 1usize << t.tau;
        for x in t.pre.iter_mut().filter(|x| !x.1) {
            x.2 = buf_range(lay, x.2, len).expect("a pre-placed C_main column is held in the small shape");
        }
    }
}

/// `Π_{lo ≤ t < hi} (1 + p_t)`: the mass of `eq(p, ·)` on the rows `< 2^lo` of a `2^hi`-row block, per row bit.
fn low_mass(p: &[F192], lo: usize, hi: usize) -> F192 {
    p[lo..hi].iter().map(|&t| F192::ONE + t).product()
}

/// `[0] ++ p`: a point of the logical table as a point of the physical one (even words).
fn even(p: &[F192]) -> Vec<F192> {
    std::iter::once(F192::ZERO).chain(p.iter().copied()).collect()
}

/// The claims of a step, made at the buffer's offsets with the big layout's points and values, on the stack that is
/// committed: unchanged in the big shape; in the small one each claim's weight moves to the even physical words and
/// its value loses `D`'s tail times `z*` (`LvmShape.onStackZ`). The order, hence every batching power, is kept.
pub fn relocate(lay: &Layout, claims: Vec<Claim>) -> Vec<Claim> {
    if !lay.small {
        return claims;
    }
    let z = z_star();
    let (dl, ln) = (lay.d_log, lay.log_n);
    let top = 1usize << (lay.nu_main + 1);
    // B1: the typed region T sits right above D (below KS): a claim is D's when it lies in D's block
    let d_hi = lay.d_off + (1usize << lay.d_vars());
    // CR-E tamper (`LVM_SH2_TAMPER=dshift`): `D`'s lane claims without the shift's coefficient (the low mass): the
    // opening proves another weight, so V_S must reject
    let dshift = std::env::var("LVM_SH2_TAMPER").is_ok_and(|v| v == "dshift");
    claims
        .into_iter()
        .map(|c| match c {
            Claim::Point { terms, mut value } => {
                let nt = terms.len();
                let terms = terms
                    .into_iter()
                    .map(|(o, p, k)| {
                        if o < d_hi && p.len() > dl {
                            // a whole `D_l` column at the big layout's point: rows < 2^18 here, the rest z*_l
                            assert!(p.len() == ln && o == lay.d(o >> dl), "a D claim is on one whole lane");
                            let m = low_mass(&p, dl, ln);
                            value += k * (F192::ONE + m).mul_base(F64(z[o >> dl]));
                            if dshift {
                                // the weight `k·eq(p_{<18}, ·)` (no low mass), its value consistent with the table,
                                // so the opening runs; V_S's weight is `m` times this one
                                assert!(nt == 1, "a D lane claim has one term");
                                value = value * m.inv();
                                return (2 * o, even(&p[..dl]), k);
                            }
                            (2 * o, even(&p[..dl]), k * m)
                        } else {
                            assert!(o.is_multiple_of(1 << p.len()) && 2 * o + (2 << p.len()) <= top, "an aligned block of the table");
                            assert!(o >= d_hi || (o & ((1 << dl) - 1)) + (1 << p.len()) <= 1 << dl, "inside one D lane");
                            (2 * o, even(&p), k)
                        }
                    })
                    .collect();
                Claim::Point { terms, value }
            }
            Claim::Ring { offset, point, slices, map, scale, mut tail } => {
                if offset >= d_hi {
                    assert!(2 * offset + (2 << point.len()) <= top, "a ring block of the table");
                    return Claim::Ring { offset: 2 * offset, point: even(&point), slices, map, scale, tail };
                }
                // `D`'s ring claim (the wire's T4): the point is `σ ‖ τ` on the big `D` block, `τ` the lane
                assert!(offset == lay.d_off && point.len() == ln + 2, "the D ring claim");
                let (sigma, tau) = point.split_at(ln);
                let m = low_mass(sigma, dl, ln);
                for (l, &zl) in z.iter().enumerate() {
                    let eq_l = (0..2).map(|b| if (l >> b) & 1 == 1 { tau[b] } else { F192::ONE + tau[b] }).product::<F192>();
                    tail.push((scale * eq_l * (F192::ONE + m), F64(zl)));
                }
                let point = [&even(&sigma[..dl])[..], tau].concat();
                Claim::Ring { offset: 2 * offset, point, slices, map, scale: scale * m, tail }
            }
        })
        .collect()
}

/// The physical table of a small-shape buffer (logical word `w` at `2w`, odd words zero): the dense reference
/// commitment (`LVM_SH2_DENSE=1`), byte-identical to the even-word one.
pub fn expand(half: &[F64]) -> Vec<F64> {
    let mut v = vec![F64::ZERO; 2 * half.len()];
    for (i, &x) in half.iter().enumerate() {
        v[2 * i] = x;
    }
    v
}

/// CR-E tamper (`LVM_SH2_ODDJUNK=1`): [`expand`] with nonzero junk in every odd word. Every small-shape weight carries
/// the factor `1 − x₀` (`LvmShape.holds_onStackZ`), so the claims' values and the proof are otherwise honest.
pub fn expand_junk(half: &[F64]) -> Vec<F64> {
    let mut v = expand(half);
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    for w in v.iter_mut().skip(1).step_by(2) {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *w = F64(x | 1);
    }
    v
}
