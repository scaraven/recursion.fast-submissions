//! B1-IE (lvm2 roll 8): the typed backend's phases on the Fiat–Shamir transcript, in V_S's order
//! (`LvmTypedV.dTypedT`, `LvmTypedVSched.phasesT` items 2–5; B1-V's toy prover `tvcheck` is the reference):
//! 1. **zerocheck**: `τ` (20 samples), 20 equality-mode rounds of `q₁, q₂` from `0`, then `a*, b*, c*`
//!    (`final = a*·b* + c*`);
//! 2. **wiring**: `γ`, 21 plain rounds of `g₀, g₂` from `a* + γb* + γ²c*` on `Σ_y u(y)·z(y)`, then `v_A, v_B, v_D,
//!    v_W` and the region values `[com, S_flat, σ′, KS]` (`final = (v_A + γv_B + γ²(v_D + v_W))·(Σ regions + virtE)`);
//! 3. **relayout**: 19 plain rounds from `v_S` on `Σ_c K(c)·C_rec(c)`, `K(sflatWord p) = eq(r_y, S_flat + p)`, then
//!    `v_R = C̃_rec(r)` (`final = relayKern(r_y, r)·v_R`);
//! 4. **A23 at `Φ_Q`**: `κ` (2), `h` (44 coefficients of `Φ_Q ∘ line`, `line(t) = a + t·(a + b)`, `a = acc_in.pt`,
//!    `b = κ ‖ r_x ‖ r_y`), `t`, one zero scalar (`h(0) = acc_in.y`, `h(1) = Σ_o eq(κ, o)·v_o`, V: `Φ_Q(line(t)) = h(t)`).
//!
//! The claims (`typedClaimsN`): on `C_rec` the relayout's point claim and `σ′`'s region claim; on `C_main` the
//! committed regions' and the `KS` aliases'. A region claim is one claim on the whole stack with the weight
//! `affW`: per region `(base, log, off)` the term `eq(r_y^{≥log}, base ≫ log) · f̃_off(r_y^{<log})`.
use std::time::Instant;

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::primitives::field::{F64, F192};
use crate::lv::primitives::multilinear::{eq_table, mle_eval_par, poly_eval};
use crate::lvm::acc::Acc;
use crate::lvm::link::Claim;
use crate::lvm::typed::{Chal, Typed, eq_o, interp_fixed, mat_vals, wiring, wiring_u, zerocheck, zerocheck_fast};

/// A region of the word space mapped to a commitment: `2^log` words from `base`, word `base + i` ↔ `off + i`
/// (B1-Q's `TReg`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TReg {
    pub base: usize,
    pub log: usize,
    pub off: usize,
}

/// **The typed phases' static data** (B1-Q's `TData`, the refreeze's): the committed regions (`C_main`), the
/// `KS` aliases (`C_main`), `σ′` (`C_rec`), `S_flat`'s base (`2^19` words, stream position `p` at `base + p`),
/// `PUB`'s base (`2^10` header lanes), the word `1`.
#[derive(Clone, Debug, Default)]
pub struct TData {
    pub com: Vec<TReg>,
    pub ks: Vec<TReg>,
    pub sig: Vec<TReg>,
    pub sflat: usize,
    pub pubb: usize,
    pub one: usize,
}

/// `Φ_Q`'s variables (`accVars` at roll 8): the selector (2), `x` (20), `y` (21).
pub const PHI_VARS: usize = 43;

/// The stream's lanes and rows (`C_rec`'s stream columns: position `p` is lane `p mod 17`, row `p div 17`).
pub const S_LANES: usize = 17;
pub const S_ROW_BITS: usize = 14;
/// `S_flat`'s positions (`2^19`) and the relayout's rounds.
pub const SFLAT_LOG: usize = 19;

/// `sflatWord` (`LvmTypedV`): the `C_rec` word of stream position `p` (the identity past the stream).
pub fn sflat_word(p: usize) -> usize {
    if p < S_LANES << S_ROW_BITS { (p % S_LANES << S_ROW_BITS) + p / S_LANES } else { p }
}

/// R9-TY: the inverse of [`sflat_word`] on `0..2^19` (a permutation: lane-major `17·2^14` words, the identity above).
pub fn sflat_inv(c: usize) -> usize {
    if c < S_LANES << S_ROW_BITS { (c & ((1 << S_ROW_BITS) - 1)) * S_LANES + (c >> S_ROW_BITS) } else { c }
}

/// `eq(r, x)` over `r.len()` bits of `x`, low first.
pub fn eq_at(r: &[F192], x: usize) -> F192 {
    r.iter().enumerate().map(|(i, &ri)| if (x >> i) & 1 == 1 { ri } else { F192::ONE + ri }).product()
}

/// The words of the virtual regions from their sources: `S_flat` (`C_rec` through `sflatWord`), `σ′` (`C_rec`),
/// `KS` (`C_main`), `PUB` (the header lanes, zero past them), `1`. Every input cell's word already holds its value
/// (`typed_lay::witness`): each must equal its source's (asserted; the alias data is the refreeze's).
pub fn fill_virtual(z: &mut [F64], set: Option<&[bool]>, td: &TData, cmain: &[F64], crec: &[F64], hdr: &[u64]) -> usize {
    let mut bad = 0usize;
    let dbg = std::env::var_os("LVM_TYPED_DEBUG").is_some();
    let mut put = |z: &mut [F64], y: usize, v: F64| {
        if set.is_some_and(|s| s[y]) && z[y] != v {
            if dbg && bad < 12 {
                eprintln!("lvm: typed: word {y} holds {:#x}, its source {:#x}", z[y].0, v.0);
            }
            bad += 1;
        }
        z[y] = v;
    };
    // (a position whose word lies past a smaller C_rec, P8's 2^18 words, reads zero)
    for p in 0..1usize << SFLAT_LOG {
        put(z, td.sflat + p, crec.get(sflat_word(p)).copied().unwrap_or(F64::ZERO));
    }
    for g in &td.sig {
        for i in 0..1usize << g.log {
            put(z, g.base + i, crec[g.off + i]);
        }
    }
    for g in &td.ks {
        for i in 0..1usize << g.log {
            put(z, g.base + i, cmain[g.off + i]);
        }
    }
    // `h`'s header lanes (14–17 from byte 8) are not compared: the typed build may run with `h = 0` (H-taint: no
    // instance reads those cells, `stream::h_sites`), and their words are `PUB`'s, set here from the real header
    for i in 0..1usize << 10 {
        let v = F64(hdr.get(i).copied().unwrap_or(0));
        if (14..18).contains(&i) {
            z[td.pubb + i] = v;
        } else {
            put(z, td.pubb + i, v);
        }
    }
    put(z, td.one, F64::ONE);
    bad
}

/// R9-TY: [`fill_virtual`] with each region's words on the pool (the regions in its order, so a word two regions
/// share ends as there; within a region the words are distinct). `LVM_TYPED_DEBUG` runs the serial version.
pub fn fill_virtual_par(z: &mut [F64], set: &[bool], td: &TData, cmain: &[F64], crec: &[F64], hdr: &[u64]) -> usize {
    if std::env::var_os("LVM_TYPED_DEBUG").is_some() {
        return fill_virtual(z, Some(set), td, cmain, crec, hdr);
    }
    const CH: usize = 1 << 13;
    // `z[base + i] = v(i)` for `i < len`, counting the set words whose value differs
    let region = |z: &mut [F64], base: usize, len: usize, v: &(dyn Fn(usize) -> F64 + Sync)| -> usize {
        let zr = &mut z[base..base + len];
        let sr = &set[base..base + len];
        let zp = crate::lv::parallel::SendPtr(zr.as_mut_ptr());
        crate::lv::parallel::map_reduce(
            len.div_ceil(CH),
            || 0usize,
            |c| {
                let (lo, hi) = (c * CH, ((c + 1) * CH).min(len));
                // SAFETY: chunk `c` owns `zr[lo..hi]`.
                let zc = unsafe { zp.slice(lo, hi - lo) };
                let mut bad = 0;
                for (i, w) in zc.iter_mut().enumerate() {
                    let x = v(lo + i);
                    bad += (sr[lo + i] && *w != x) as usize;
                    *w = x;
                }
                bad
            },
            |a, b| a + b,
        )
    };
    let mut bad = region(z, td.sflat, 1 << SFLAT_LOG, &|p| crec.get(sflat_word(p)).copied().unwrap_or(F64::ZERO));
    for g in &td.sig {
        bad += region(z, g.base, 1 << g.log, &|i| crec[g.off + i]);
    }
    for g in &td.ks {
        bad += region(z, g.base, 1 << g.log, &|i| cmain[g.off + i]);
    }
    for i in 0..1usize << 10 {
        let v = F64(hdr.get(i).copied().unwrap_or(0));
        if !(14..18).contains(&i) && set[td.pubb + i] && z[td.pubb + i] != v {
            bad += 1;
        }
        z[td.pubb + i] = v;
    }
    if set[td.one] && z[td.one] != F64::ONE {
        bad += 1;
    }
    z[td.one] = F64::ONE;
    bad
}

/// `C_main`'s committed regions written from `z` (`C_main[off + i] = z[base + i]`).
pub fn place_com(z: &[F64], td: &TData, cmain: &mut [F64]) {
    for g in &td.com {
        cmain[g.off..g.off + (1 << g.log)].copy_from_slice(&z[g.base..g.base + (1 << g.log)]);
    }
}

/// R9-TY: [`place_com`] with each region copied on the pool (the regions in order).
pub fn place_com_par(z: &[F64], td: &TData, cmain: &mut [F64]) {
    const CH: usize = 1 << 15;
    for g in &td.com {
        let dst = &mut cmain[g.off..g.off + (1 << g.log)];
        let src = &z[g.base..g.base + (1 << g.log)];
        crate::lv::parallel::chunks_mut(dst, CH, |c, d| d.copy_from_slice(&src[c * CH..c * CH + d.len()]));
    }
}

/// `Σ_{y ∈ regions} eq(r_y, y)·z(y)` over `regions` given as `(base, log)`.
fn reg_value(z: &[F64], ry: &[F192], regs: &[(usize, usize)]) -> F192 {
    regs.iter().map(|&(base, log)| eq_at(&ry[log..], base >> log) * mle_eval_par(&z[base..base + (1 << log)], &ry[..log])).sum()
}

/// A region claim (`affW`): per region the term at its target `off` with the point `r_y^{<log}` and the weight
/// `eq(r_y^{≥log}, base ≫ log)`.
fn reg_claim(regs: &[TReg], ry: &[F192], value: F192) -> Claim {
    Claim::Point { terms: regs.iter().map(|g| (g.off, ry[..g.log].to_vec(), eq_at(&ry[g.log..], g.base >> g.log))).collect(), value }
}

/// The prover's tamper modes (`LVM_TYPED_TAMPER`, dev; every one must be rejected by V_S): `h1` (one coefficient
/// of `h` moved: `h(1)` fails), `h2` (two coefficients moved, the sum kept: only `Φ_Q` catches it), `vs` (`v_S`
/// moved: the wiring's final check fails).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tamper {
    None,
    H1,
    H2,
    Vs,
}

pub fn tamper() -> Tamper {
    match std::env::var("LVM_TYPED_TAMPER").as_deref() {
        Ok("h1") => Tamper::H1,
        Ok("h2") => Tamper::H2,
        Ok("vs") => Tamper::Vs,
        _ => Tamper::None,
    }
}

/// What the typed phases leave: the outgoing accumulator, the claims, the challenges (for tests), timings.
pub struct TypedOut {
    pub acc_out: Acc,
    /// `C_rec`: the relayout's point claim, `σ′`'s region claim.
    pub rec_claims: Vec<Claim>,
    /// `C_main`: the committed regions' claim, the `KS` aliases' claim.
    pub main_claims: Vec<Claim>,
    pub rx: Vec<F192>,
    pub ry: Vec<F192>,
    pub v: [F192; 4],
    pub stages: Vec<(&'static str, f64)>,
}

/// **The typed phases** on `ps` (B-DES §1.2; V_S `dTypedT` without the mini-bus): `b1` the matrices (with the class
/// kernels when built), `z` the word vector (virtual regions filled), `crec` the committed `C_rec`, `acc_in` the
/// header's accumulator (43 coordinates). `general`: the zerocheck on `(D + W)z` as given (a tampered witness's
/// zerocheck is honest about it), else the honest prover's `C = A∘B`.
pub fn prove(ps: &mut ProverState, b1: &Typed, z: &[F64], td: &TData, crec: &[F64], acc_in: &Acc, general: bool, phi_true: Option<&Typed>) -> TypedOut {
    let tm = tamper();
    let mut stages = Vec::new();
    let mut t = Instant::now();
    let prof = crate::lv::tracing::enabled();
    let mut c0 = if prof { crate::lv::tracing::cpu_now() } else { (0.0, 0.0) };
    let mut lap = |n: &'static str, st: &mut Vec<(&'static str, f64)>| {
        let s = t.elapsed().as_secs_f64();
        if prof {
            let c = crate::lv::tracing::cpu_now();
            eprintln!("  PCPU {n:<14} wall {s:.4} cpu {:.4}", c.0 - c0.0);
            c0 = c;
        }
        st.push((n, s));
        t = Instant::now();
    };
    // 1. zerocheck
    let tau = ps.sample_vec(b1.x_log);
    let zc = if general { zerocheck(b1.abc(z), &tau, ps) } else { zerocheck_fast(b1.ab_vals(z), &tau, b1.x_live, ps) };
    ps.add_scalars(&[zc.a, zc.b, zc.c]);
    lap("zerocheck", &mut stages);
    // 2. wiring
    let gamma = ps.sample();
    let mut tp = Instant::now();
    let u = wiring_u(b1, &zc.r, gamma);
    crate::lvm::stream::part("wr u", &mut tp);
    let wr = wiring(u, z, zc.a + gamma * zc.b + gamma * gamma * zc.c, b1.y_live, ps);
    crate::lvm::stream::part("wr sc", &mut tp);
    let (rx, ry) = (zc.r.clone(), wr.r.clone());
    let v = match &b1.phik {
        Some(pk) => {
            let pt: Vec<F192> = [&[F192::ZERO, F192::ZERO][..], &rx, &ry].concat();
            let m = pk.mats(std::slice::from_ref(&pt));
            [m[0], m[1], m[2], m[3]]
        }
        None => mat_vals(b1, &rx, &ry),
    };
    crate::lvm::stream::part("wr mats", &mut tp);
    let rr = |g: &[TReg]| g.iter().map(|g| (g.base, g.log)).collect::<Vec<_>>();
    let v_com = reg_value(z, &ry, &rr(&td.com));
    let mut v_s = reg_value(z, &ry, &[(td.sflat, SFLAT_LOG)]);
    let v_sig = reg_value(z, &ry, &rr(&td.sig));
    let v_ks = reg_value(z, &ry, &rr(&td.ks));
    if tm == Tamper::Vs {
        v_s += F192::ONE;
    }
    crate::lvm::stream::part("wr regs", &mut tp);
    ps.add_scalars(&v);
    ps.add_scalars(&[v_com, v_s, v_sig, v_ks]);
    lap("wiring", &mut stages);
    // 3. relayout: K(sflatWord p) = eq(r_y, S_flat + p) on C_rec's 2^19 words
    let nr = crec.len().trailing_zeros() as usize;
    assert_eq!(nr, SFLAT_LOG, "C_rec has 2^19 words (the relayout's rounds)");
    let mut tp = Instant::now();
    let w_hi = eq_at(&ry[SFLAT_LOG..], td.sflat >> SFLAT_LOG);
    // R9-TY: `w_hi·eq(r_y, ·)` as one seeded table, then `K` gathered by `sflatWord`'s inverse on the pool (it was a
    // serial scatter of 2^19 products); `LVM_TYPED_WREF=1`: the scatter
    let k = if std::env::var("LVM_TYPED_WREF").is_ok_and(|v| v == "1") {
        let e = eq_table(&ry[..SFLAT_LOG]);
        let mut k = vec![F192::ZERO; 1 << nr];
        for (p, &ep) in e.iter().enumerate() {
            k[sflat_word(p)] = w_hi * ep;
        }
        k
    } else {
        // SAFETY: `fill_eq_table` writes every element.
        let e = unsafe { crate::lv::primitives::filled_vec(1usize << SFLAT_LOG, |o: &mut [F192]| crate::lv::primitives::multilinear::fill_eq_table(&ry[..SFLAT_LOG], w_hi, o)) };
        // SAFETY: `fill` writes every element; `sflat_inv` is `sflat_word`'s inverse on `0..2^19`.
        unsafe { crate::lv::primitives::filled_vec(1usize << nr, |k: &mut [F192]| crate::lv::parallel::fill(k, |c| e[sflat_inv(c)])) }
    };
    crate::lvm::stream::part("rl k", &mut tp);
    let rl = wiring(k, crec, v_s, 1 << nr, ps);
    crate::lvm::stream::part("rl sc", &mut tp);
    let v_r = rl.z;
    ps.add_scalar(v_r);
    lap("relayout", &mut stages);
    // 4. A23 at Φ_Q
    let kappa = ps.sample_vec(2);
    let eo = eq_o(&kappa);
    let y_own: F192 = (0..4).map(|o| eo[o] * v[o]).sum();
    let b: Vec<F192> = [&kappa[..], &rx, &ry].concat();
    let d = acc_in.pt.len();
    assert_eq!(d, b.len(), "acc_in has 2 + 20 + 21 = 43 coordinates");
    let pts: Vec<Vec<F192>> = (2..=d as u64).map(|j| crate::lvm::acc::line(&acc_in.pt, &b, F192::new(j, 0, 0))).collect();
    // `h` interpolates `Φ_Q` on the line; with `phi_true` (the operand tampers: `b1` is the prover's own wrong
    // matrices) the true `Φ_Q`'s line plus `δ·t`, `δ = y_own + Φ_Q(b)`, so that `h(0) = acc_in.y` and `h(1) = y_own`
    // pass and only V's `Φ_Q(acc_out) = h(t)` can catch it (B1-V's `tvcheck` tamper)
    let ph = phi_true.unwrap_or(b1);
    let eval = |pts: &[Vec<F192>]| match &ph.phik {
        Some(pk) => pk.eval(pts),
        None => crate::lvm::typed::phi_multi(ph, pts),
    };
    let (y1, delta) = match phi_true {
        Some(_) => {
            let pb = eval(std::slice::from_ref(&b))[0];
            (pb, y_own + pb)
        }
        None => (y_own, F192::ZERO),
    };
    let mut tp = Instant::now();
    let mut ys = vec![acc_in.y, y1];
    ys.extend(eval(&pts));
    crate::lvm::stream::part("acc eval", &mut tp);
    let mut h = interp_fixed(&ys);
    h[1] += delta;
    match tm {
        Tamper::H1 => h[7] += F192::ONE,
        Tamper::H2 => {
            h[7] += F192::ONE;
            h[9] += F192::ONE;
        }
        _ => {}
    }
    ps.add_scalars(&h);
    let tt = ps.sample();
    ps.add_scalar(F192::ZERO);
    let acc_out = Acc { pt: crate::lvm::acc::line(&acc_in.pt, &b, tt), y: poly_eval(&h, tt) };
    lap("acc", &mut stages);
    let rec_claims = vec![Claim::point(0, rl.r.clone(), v_r), reg_claim(&td.sig, &ry, v_sig)];
    let main_claims = vec![reg_claim(&td.com, &ry, v_com), reg_claim(&td.ks, &ry, v_ks)];
    TypedOut { acc_out, rec_claims, main_claims, rx, ry, v, stages }
}

impl TData {
    /// `com|ks|sig base log off` lines, `sflat base`, `pub base`, `one word`.
    pub fn parse(text: &str) -> TData {
        let mut td = TData::default();
        for l in text.lines() {
            let t: Vec<&str> = l.split_whitespace().collect();
            let n = |i: usize| -> usize { t[i].parse().unwrap_or_else(|_| panic!("tdata: {l:?}")) };
            match t.first() {
                Some(&"com") => td.com.push(TReg { base: n(1), log: n(2), off: n(3) }),
                Some(&"ks") => td.ks.push(TReg { base: n(1), log: n(2), off: n(3) }),
                Some(&"sig") => td.sig.push(TReg { base: n(1), log: n(2), off: n(3) }),
                Some(&"sflat") => td.sflat = n(1),
                Some(&"pub") => td.pubb = n(1),
                Some(&"one") => td.one = n(1),
                None => {}
                Some(x) => panic!("tdata: line tag {x:?}"),
            }
        }
        td
    }
}

/// **`accOutOf` of a typed proof** (A23 at `Φ_Q`; `LvmTypedV.accOutOfT`): its trace read as `dTypedT` reads it up to
/// `t` (the caps, `τ`, the zerocheck's rounds, `a*, b*, c*`, `γ`, the wiring's rounds, the 8 values, the relayout's
/// rounds, `v_R`, `κ`, `h`, `t`); the folded claim `(line(acc_in.pt, κ ‖ r_x ‖ r_y)(t), h(t))`.
pub fn acc_out_of(acc_in: &Acc, tr: &[(Vec<u8>, crate::oracle::Digest)]) -> Acc {
    let (mut ent, mut msg) = (2usize, 0usize);
    let lanes3 = |b: &[u8], o: usize| {
        let l = |i: usize| b.get(o + 8 * i..o + 8 * i + 8).map_or(0, |x| u64::from_le_bytes(x.try_into().unwrap()));
        F192::new(l(0), l(1), l(2))
    };
    let mut read = |ent: usize, msg: &mut usize| {
        let v = lanes3(&tr[ent].0, 32 + *msg);
        *msg += 24;
        v
    };
    let mut sample = |ent: &mut usize, msg: &mut usize| {
        let v = lanes3(&tr[*ent].1, 0);
        *ent += 1;
        *msg = 0;
        v
    };
    for _ in 0..20 {
        sample(&mut ent, &mut msg);
    }
    let mut rounds = |k: usize, ent: &mut usize, msg: &mut usize| -> Vec<F192> {
        (0..k)
            .map(|_| {
                read(*ent, msg);
                read(*ent, msg);
                sample(ent, msg)
            })
            .collect()
    };
    let rx = rounds(20, &mut ent, &mut msg);
    for _ in 0..3 {
        read(ent, &mut msg);
    }
    sample(&mut ent, &mut msg);
    let ry = rounds(21, &mut ent, &mut msg);
    for _ in 0..8 {
        read(ent, &mut msg);
    }
    rounds(SFLAT_LOG, &mut ent, &mut msg);
    read(ent, &mut msg);
    let kappa = [sample(&mut ent, &mut msg), sample(&mut ent, &mut msg)];
    let h: Vec<F192> = (0..PHI_VARS + 1).map(|_| read(ent, &mut msg)).collect();
    let t = sample(&mut ent, &mut msg);
    let b: Vec<F192> = [&kappa[..], &rx, &ry].concat();
    Acc { pt: crate::lvm::acc::line(&acc_in.pt, &b, t), y: poly_eval(&h, t) }
}
