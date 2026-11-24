//! The typed phases' witness: the words `z : 2^21 → K` (Lean `zOf`) and the typed result memory `T` on the stack.
//!
//! [`witness`] reads the words the circuit takes from the stack (`ks` from their stack words, `sflat` and `sigma`
//! from `C_rec`'s window), the public ones (`pub`, `qlt`, `one`), solves the defining rows in the blob's `OUT`
//! order (row `x` gives word `y = (A·B + C')/c_y`, `C'` the rest of `M_2 z + M_3 z`), then writes every `com` word
//! to its stack word (`T`). It writes nothing else: `X`'s words, the mini-bus columns and every other block are
//! left as they are. A `com` word no row defines is zero (FORMAT6 §2.1).

use primitives::field::{F64, F128};

use crate::circuit::{AuxBits, BOut, Circuit, Csum, PowBits, REC_BASE, Src, X_VARS, Y_VARS};

/// The words and the public lanes they were built from.
pub struct TypedWitness<'c> {
    pub circ: &'c Circuit,
    /// `z(y)`, `2^21` words.
    pub z: Vec<F64>,
    /// `PUB`'s lanes (`pub`'s word `base + i` is lane `i`).
    pub pub_words: Vec<u64>,
    /// R7: the sponge message cells `X` the witness defined (stack index, value), for the caller to write before the
    /// sponge rows are generated again ([`SpongeLink`]); empty without a link.
    pub x_writes: Vec<(usize, F64)>,
}

/// R7 (KSA's `ks` re-split): the node's sponge rows from `split` on absorb `X`, which `Q` reads as `ks` aliases, and
/// their outputs `Y` feed `Q` through `ks` aliases again; `X(i, l)` is the `com` word `c` of its copy row
/// (`D: c + X-alias, W: diff`). The witness runs those rows itself, in the dependency order, as one step a row.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpongeLink {
    /// `cont[x]`: row `x` continues row `x − 1` (FORMAT6 §6.3 `contRows`).
    pub cont: Vec<bool>,
    /// Per row `split + i`: the source word of each message lane (`None`: the stack's cell as it is).
    pub xsrc: Vec<[Option<u32>; r3core::layout::MSG_LANES]>,
    /// Per row `split + i`: the `ks` alias words of its `X` cells, `(lane, word)`.
    pub xal: Vec<Vec<(usize, u32)>>,
    /// Per row `split + i`: the `ks` alias words of its output lanes, `(lane, word)`.
    pub yal: Vec<Vec<(usize, u32)>>,
}

/// The link of `circ`, if it reads any `X` cell through `ks` (none for the stub and the older blobs).
pub fn sponge_link(circ: &Circuit, cont_rows: &[usize]) -> Option<SpongeLink> {
    use r3core::layout::{MSG_LANES, SLOT_Y, SP_LOG, SP_ROWS, SPLIT, XL, idx, x_idx};
    let n = 1usize << XL;
    let (x0, x1) = (x_idx(0, 0), x_idx(0, MSG_LANES));
    let y0 = idx(SLOT_Y, 0);
    let mut l = SpongeLink { cont: vec![false; SP_ROWS], xsrc: vec![[None; MSG_LANES]; n], xal: vec![Vec::new(); n], yal: vec![Vec::new(); n] };
    cont_rows.iter().for_each(|&x| l.cont[x] = true);
    let mut alias_x: std::collections::HashMap<u32, (usize, usize)> = std::collections::HashMap::new();
    for r in circ.regs_of(Src::Ks) {
        for k in 0..r.len() {
            let (t, a) = (r.stack_idx(k), (r.base + k) as u32);
            if (x0..x1).contains(&t) {
                let (i, lane) = ((t - x0) % n, (t - x0) >> XL);
                l.xal[i].push((lane, a));
                alias_x.insert(a, (i, lane));
            } else if t >= y0 && t < y0 + (25 << SP_LOG) {
                let (row, lane) = ((t - y0) & (SP_ROWS - 1), (t - y0) >> SP_LOG);
                if row >= SPLIT {
                    l.yal[row - SPLIT].push((lane, a));
                }
            }
        }
    }
    if alias_x.is_empty() {
        return None;
    }
    // the blob's explicit sources (`XSRC`), if any; else the copy rows
    let explicit = crate::circuit::xsrc_of(circ);
    if !explicit.is_empty() {
        explicit.iter().for_each(|&(i, lane, y)| l.xsrc[i][lane] = Some(y));
        return Some(l);
    }
    // copy rows: exactly `D: c + a` (`a` an X alias, `c` a com word), `W: d` (com), unit coefficients
    let is_com = |y: u32| matches!(circ.src_of(y as usize), Some((Src::Com, _)));
    let mut i = 0;
    while i < circ.ents.len() {
        let x = circ.ents[i].x;
        let row = circ.row(x);
        i += row.len();
        if row.len() != 3 || row.iter().any(|e| e.c != F128::ONE) {
            continue;
        }
        let ds: Vec<u32> = row.iter().filter(|e| e.o == 2).map(|e| e.y).collect();
        let ws: Vec<u32> = row.iter().filter(|e| e.o == 3).map(|e| e.y).collect();
        if ds.len() != 2 || ws.len() != 1 || !is_com(ws[0]) {
            continue;
        }
        for (a, c) in [(ds[0], ds[1]), (ds[1], ds[0])] {
            if let Some(&(xi, lane)) = alias_x.get(&a)
                && is_com(c)
                && l.xsrc[xi][lane].is_none()
            {
                l.xsrc[xi][lane] = Some(c);
            }
        }
    }
    Some(l)
}

/// `HDR` as `PUB`'s lanes: 8 bytes LE a lane (`|HDR| = 824`: 103 lanes).
pub fn pub_lanes(hdr: &[u8]) -> Vec<u64> {
    assert!(hdr.len() % 8 == 0, "HDR is whole lanes");
    hdr.chunks_exact(8).map(|b| u64::from_le_bytes(b.try_into().unwrap())).collect()
}

/// Why a witness is not one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessError {
    /// Row `x`'s defining value of word `y` is not in `K`.
    NotK { x: u32, y: u32 },
    /// The relation fails at slot `x` (after solving: an inconsistent input).
    Relation { x: u32 },
    /// The `OUT` definitions are cyclic.
    Cycle,
}

/// Build the witness and write `T` into `stack` (`2^25` words); the PoW bit words are the circuit's if it is the
/// one in use ([`crate::circuit::pow_bits_of`]).
pub fn witness<'c>(circ: &'c Circuit, stack: &mut [F64], pub_words: &[u64]) -> Result<TypedWitness<'c>, WitnessError> {
    let aux = Aux { bits: crate::circuit::aux_bits_of(circ), bout: crate::circuit::bout_of(circ), link: None, csum: crate::circuit::csum_of(circ), readd: None };
    witness_full(circ, crate::circuit::pow_bits_of(circ), aux, stack, pub_words)
}

/// [`witness`] with the node's sponge link (R7): `cont_rows` is FORMAT6 §6.3's `contRows`. The caller writes
/// `x_writes` into the stack and generates the sponge rows again.
pub fn witness_linked<'c>(circ: &'c Circuit, stack: &mut [F64], pub_words: &[u64], link: Option<&SpongeLink>) -> Result<TypedWitness<'c>, WitnessError> {
    let readd = readd_link(circ, stack);
    let aux = Aux { bits: crate::circuit::aux_bits_of(circ), bout: crate::circuit::bout_of(circ), link, csum: crate::circuit::csum_of(circ), readd: readd.as_ref() };
    witness_full(circ, crate::circuit::pow_bits_of(circ), aux, stack, pub_words)
}

/// The derived words of F2 (NODE3's export): `BITS` aux rows and `BOUT` lines.
#[derive(Clone, Copy, Debug, Default)]
pub struct Aux<'a> {
    pub bits: &'a [AuxBits],
    pub bout: &'a [BOut],
    /// R7: the node's sponge link ([`sponge_link`]), if `Q` reads `X` through `ks`.
    pub link: Option<&'a SpongeLink>,
    /// R7: the WOTS checksum lines (`CSUM`).
    pub csum: &'a [Csum],
    /// R7: the mini-bus reads' value words as memory reads ([`readd_link`]).
    pub readd: Option<&'a Readd>,
}

/// R7 (MBT's semantics, season 1's): every mini-bus read (a `readd` iteration of the circuit, padded rows included)
/// reads memory: its value word is the seeded cell's value at the address the row computed (`g^cell`; the seeds'
/// cells are `STREAM` words). These words are memory reads, not `OUT` solutions (on padded rows the gated path rows
/// would solve them to data that is not the cell's): their `OUT` entries are dropped and a `Readd` step defines them
/// once the address word is known.
#[derive(Clone, Debug, Default)]
pub struct Readd {
    /// `(address word, value word)` per read row.
    pub pairs: Vec<(u32, u32)>,
    /// Seeded memory: address `g^cell` → value.
    pub mem: std::collections::HashMap<u64, u64>,
}

/// The read rows of the blob's `MINIBUS` section and the seeded memory on `stack` (`STREAM` written), if the circuit
/// in use has a `MINIBUS` section.
pub fn readd_link(circ: &Circuit, stack: &[F64]) -> Option<Readd> {
    let pairs = readd_pairs(circ)?;
    let m = crate::circuit::minibus()?;
    let mut rd = Readd { pairs, ..Readd::default() };
    for (limbs, base, stride, tau, v, _) in &m.seeds {
        assert_eq!(*limbs, 1, "K cells");
        let step = primitives::field::g_pow(*stride);
        let mut a = primitives::field::g_pow(*base);
        for x in 0..1usize << tau {
            assert!(rd.mem.insert(a.0, stack[v[0] + x].0).is_none(), "a cell is seeded once");
            a = a * step;
        }
    }
    Some(rd)
}

/// The `(address word, value word)` pairs of [`readd_link`] (static: no stack), if the circuit in use has a `MINIBUS`
/// section and `circ` is it.
pub fn readd_pairs(circ: &Circuit) -> Option<Vec<(u32, u32)>> {
    let m = crate::circuit::minibus()?;
    if !std::ptr::eq(crate::circuit::circuit(), circ) {
        return None;
    }
    let word_of = |at: usize| -> u32 {
        let r = circ.regs_of(Src::Com).find(|r| (r.off..r.off + r.len()).contains(&at)).expect("a mini-bus read column is a com word");
        (r.base + at - r.off) as u32
    };
    let mut pairs = Vec::new();
    for (limbs, tau, addr, v, _) in &m.reads {
        assert_eq!(*limbs, 1, "K cells");
        for x in 0..1usize << tau {
            pairs.push((word_of(addr + x), word_of(v[0] + x)));
        }
    }
    Some(pairs)
}

/// R8: the witness plan of the circuit in use ([`solve_plan_aux`] with its own aux rows, its sponge link and its
/// mini-bus read pairs), computed once by [`prewarm`] (before `ready`): it depends on `Q` only, not on the stack.
struct Cached {
    link: Option<SpongeLink>,
    pairs: Option<Vec<(u32, u32)>>,
    plan: Vec<Step>,
}

static PLAN: std::sync::OnceLock<Option<Cached>> = std::sync::OnceLock::new();

/// Compute and keep the plan of the circuit in use for the sponge link of `cont_rows` (FORMAT6 §6.3 `contRows`).
/// Returns the seconds it took (0 if already done). A cyclic `Q` keeps no plan (the witness reports it).
pub fn prewarm(cont_rows: &[usize]) -> f64 {
    let t = std::time::Instant::now();
    let mut did = false;
    PLAN.get_or_init(|| {
        did = true;
        let circ = crate::circuit::circuit();
        let link = sponge_link(circ, cont_rows);
        let pairs = readd_pairs(circ);
        let rd = pairs.clone().map(|pairs| Readd { pairs, ..Readd::default() });
        let aux = Aux { bits: crate::circuit::aux_bits_of(circ), bout: crate::circuit::bout_of(circ), link: link.as_ref(), csum: crate::circuit::csum_of(circ), readd: rd.as_ref() };
        solve_plan_aux(circ, aux).ok().map(|plan| Cached { link, pairs, plan })
    });
    if did { t.elapsed().as_secs_f64() } else { 0.0 }
}

/// The same slice (address and length).
fn same<T>(a: &[T], b: &[T]) -> bool {
    a.len() == b.len() && std::ptr::eq(a.as_ptr(), b.as_ptr())
}

/// The kept plan, if it is the one [`solve_plan_aux`] would compute for `(circ, aux)`: the circuit in use, its own
/// aux rows (the same slices), the same sponge link and read pairs.
fn cached_plan(circ: &Circuit, aux: &Aux) -> Option<&'static [Step]> {
    let c = PLAN.get()?.as_ref()?;
    let ok = std::ptr::eq(crate::circuit::circuit(), circ)
        && same(aux.bits, crate::circuit::aux_bits_of(circ))
        && same(aux.bout, crate::circuit::bout_of(circ))
        && same(aux.csum, crate::circuit::csum_of(circ))
        && aux.link == c.link.as_ref()
        && aux.readd.map(|r| &r.pairs) == c.pairs.as_ref();
    ok.then_some(c.plan.as_slice())
}

/// [`witness`] with explicit PoW bit words: word `bw + i` = bit `i` of `C_rec` (`STREAM`) word `w`, written before
/// the rows are solved (a function of the child's trace: zero at `b = 0`).
pub fn witness_with<'c>(circ: &'c Circuit, pow: &[PowBits], stack: &mut [F64], pub_words: &[u64]) -> Result<TypedWitness<'c>, WitnessError> {
    witness_full(circ, pow, Aux::default(), stack, pub_words)
}

/// [`witness_with`] with F2's derived words (`BITS`: word `dst[i]` = bit `i` of word `y`; `BOUT`), written in the
/// dependency order.
pub fn witness_full<'c>(
    circ: &'c Circuit,
    pow: &[PowBits],
    aux: Aux,
    stack: &mut [F64],
    pub_words: &[u64],
) -> Result<TypedWitness<'c>, WitnessError> {
    let (z, not_k, x_writes) = solve_z(circ, pow, aux, stack, pub_words, true)?;
    if let Some(&(x, y)) = not_k.first() {
        return Err(WitnessError::NotK { x, y });
    }
    if let Some(x) = first_violation(circ, &z) {
        return Err(WitnessError::Relation { x });
    }
    for r in circ.regs_of(Src::Com) {
        let lo = r.stack_idx(0);
        stack[lo..lo + r.len()].copy_from_slice(&z[r.base..r.base + r.len()]);
    }
    Ok(TypedWitness { circ, z, pub_words: pub_words.to_vec(), x_writes })
}

/// The words: the read ones, the PoW bit words, then the `OUT` rows in a dependency order. `strict`: stop at the
/// first row whose solution is not in `K`; else (dev) leave its words zero and list it.
fn solve_z(
    circ: &Circuit,
    pow: &[PowBits],
    aux: Aux,
    stack: &[F64],
    pub_words: &[u64],
    strict: bool,
) -> Result<(Vec<F64>, Vec<(u32, u32)>, Vec<(usize, F64)>), WitnessError> {
    assert_eq!(stack.len(), 1 << r3core::layout::STACK_LOG);
    let mut z = vec![F64::ZERO; 1 << Y_VARS];
    for r in &circ.regs {
        let words = &mut z[r.base..r.base + r.len()];
        match r.src {
            Src::Ks | Src::Sflat | Src::Sigma => {
                let lo = r.stack_idx(0);
                words.copy_from_slice(&stack[lo..lo + r.len()]);
            }
            Src::Pub => words.iter_mut().enumerate().for_each(|(i, w)| *w = F64(pub_words.get(i).copied().unwrap_or(0))),
            Src::Qlt => words.iter_mut().enumerate().for_each(|(i, w)| *w = F64(circ.qlt_word(r.base + i))),
            Src::One => words.fill(F64::ONE),
            Src::Com => words.fill(F64::ZERO),
        }
    }
    for p in pow {
        let v = stack[REC_BASE + p.w].0;
        for i in 0..p.nb {
            let y = p.bw + i;
            assert!(matches!(circ.src_of(y), Some((Src::Com, _))), "PoW bit word {y}: not a com word");
            z[y] = F64(v >> i & 1);
        }
    }
    // the rows in a dependency order (the blob's `OUT` order need not be one), each row's `OUT` words together:
    // one word (`y = v/c_y ∈ K`) or an `E` twin row of two (`c_a·y_a + c_b·y_b = v` over `K`, CD's form `c_a = 1`,
    // `c_b = y`: `y_a = v.c0`, `y_b = v.c1`)
    let mut not_k = Vec::new();
    // the link's rows from `split` on: their outputs as they are computed (row `split − 1`'s from the stack)
    use r3core::layout::{MSG_LANES, SPLIT, x_idx, y_idx};
    let mut ycur: Vec<[u64; 25]> = if aux.link.is_some() { vec![[0; 25]; 1 << r3core::layout::XL] } else { Vec::new() };
    let owned;
    let plan: &[Step] = match cached_plan(circ, &aux) {
        Some(p) => p,
        None => {
            owned = solve_plan_aux(circ, aux)?;
            &owned
        }
    };
    for step in plan {
        let (x, ys) = match *step {
            Step::Sponge(i) => {
                let l = aux.link.unwrap();
                let r = SPLIT + i;
                let mut s: [u64; 25] = if !l.cont[r] {
                    [0; 25]
                } else if i == 0 {
                    std::array::from_fn(|lane| stack[y_idx(r - 1, lane)].0)
                } else {
                    ycur[i - 1]
                };
                for lane in 0..MSG_LANES {
                    let m = l.xsrc[i][lane].map_or(stack[x_idx(i, lane)].0, |c| z[c as usize].0);
                    s[lane] ^= m;
                }
                for &(lane, a) in &l.xal[i] {
                    z[a as usize] = F64(l.xsrc[i][lane].map_or(stack[x_idx(i, lane)].0, |c| z[c as usize].0));
                }
                primitives::hash::keccak_f(&mut s);
                ycur[i] = s;
                for &(lane, a) in &l.yal[i] {
                    z[a as usize] = F64(s[lane]);
                }
                continue;
            }
            Step::BOut(k) => {
                let b = &aux.bout[k];
                z[b.d as usize] = F64(b.apply(z[b.y as usize].0));
                continue;
            }
            Step::Readd(k) => {
                let rd = aux.readd.unwrap();
                let (a, v) = rd.pairs[k];
                match rd.mem.get(&z[a as usize].0) {
                    Some(&m) => z[v as usize] = F64(m),
                    None => {
                        // an address that is no seeded cell: no memory value (the bus rejects it)
                        not_k.push((u32::MAX, v));
                        if strict {
                            break;
                        }
                    }
                }
                continue;
            }
            Step::Csum(k) => {
                let cs = &aux.csum[k];
                let v = cs.value(&z);
                for b in 0..64 {
                    z[(cs.bw + b) as usize] = F64(v >> b & 1);
                }
                for (b, &w) in cs.c.iter().enumerate() {
                    z[w as usize] = F64(v >> b & 1);
                }
                continue;
            }
            Step::Bits(k) => {
                let b = &aux.bits[k];
                let v = z[b.y as usize].0;
                for (i, d) in b.dst.iter().enumerate() {
                    if let Some(d) = *d {
                        z[d as usize] = F64(v >> i & 1);
                    }
                }
                continue;
            }
            Step::Row(x, ref ys) => (x, ys),
        };
        let (mut a, mut b, mut c) = (F128::ZERO, F128::ZERO, F128::ZERO);
        let mut cy = vec![F128::ZERO; ys.len()];
        for e in circ.row(x) {
            match e.o {
                0 => a += e.c.mul_base(z[e.y as usize]),
                1 => b += e.c.mul_base(z[e.y as usize]),
                _ => match ys.iter().position(|&y| y == e.y) {
                    Some(i) => cy[i] += e.c,
                    None => c += e.c.mul_base(z[e.y as usize]),
                },
            }
        }
        let v = a * b + c;
        match solve_k(&cy, v) {
            Some(sol) => ys.iter().zip(sol).for_each(|(&y, w)| z[y as usize] = w),
            None => {
                not_k.push((x, ys[0]));
                if strict {
                    break;
                }
            }
        }
    }
    let x_writes = aux.link.map_or(Vec::new(), |l| {
        (0..1usize << r3core::layout::XL)
            .flat_map(|i| (0..MSG_LANES).filter_map(move |lane| l.xsrc[i][lane].map(|c| (i, lane, c))))
            .map(|(i, lane, c)| (x_idx(i, lane), z[c as usize]))
            .collect()
    });
    Ok((z, not_k, x_writes))
}

/// Dev (R7): the `X` cells a non-strict solve defines (for checks when the witness fails).
pub fn x_writes_dev(circ: &Circuit, stack: &[F64], pub_words: &[u64], link: &SpongeLink) -> Vec<(usize, F64)> {
    let readd = readd_link(circ, stack);
    let aux = Aux { bits: crate::circuit::aux_bits_of(circ), bout: crate::circuit::bout_of(circ), link: Some(link), csum: crate::circuit::csum_of(circ), readd: readd.as_ref() };
    solve_z(circ, crate::circuit::pow_bits_of(circ), aux, stack, pub_words, false).map(|r| r.2).unwrap_or_default()
}

/// Dev (R7): every violated slot of the relation on `stack`/`pub_words` (the first 40 in full: each entry's matrix,
/// word, region, index in it, value, and the `OUT` row defining it, if any), and the rows whose solution is not in
/// `K`.
pub fn diagnose(circ: &Circuit, stack: &[F64], pub_words: &[u64], link: Option<SpongeLink>) -> String {
    use std::fmt::Write;
    let pow = crate::circuit::pow_bits_of(circ);
    let mut s = String::new();
    let bits = crate::circuit::aux_bits_of(circ);
    let readd = readd_link(circ, stack);
    let aux = Aux { bits, bout: crate::circuit::bout_of(circ), link: link.as_ref(), csum: crate::circuit::csum_of(circ), readd: readd.as_ref() };
    let (z, not_k, _) = match solve_z(circ, pow, aux, stack, pub_words, false) {
        Ok(v) => v,
        Err(e) => return format!("diagnose: {e:?}"),
    };
    let def: std::collections::HashMap<u32, u32> = circ.outs.iter().map(|&(x, y)| (y, x)).collect();
    let bitw: std::collections::HashMap<u32, u32> =
        bits.iter().flat_map(|b| b.dst.iter().flatten().map(move |&d| (d, b.y))).chain(aux.bout.iter().map(|b| (b.d, b.y))).collect();
    writeln!(s, "diagnose: {} rows not in K: {:?}", not_k.len(), &not_k[..not_k.len().min(20)]).unwrap();
    if let Some(l) = aux.link {
        let al: usize = l.xal.iter().map(|v| v.len()).sum();
        let lanes: std::collections::BTreeSet<(usize, usize)> = l.xal.iter().enumerate().flat_map(|(i, v)| v.iter().map(move |&(ln, _)| (i, ln))).collect();
        let src = l.xsrc.iter().map(|a| a.iter().flatten().count()).sum::<usize>();
        let nosrc: Vec<(usize, usize)> = lanes.iter().copied().filter(|&(i, ln)| l.xsrc[i][ln].is_none()).collect();
        let yal: usize = l.yal.iter().map(|v| v.len()).sum();
        writeln!(s, "diagnose: link: {al} X alias words on {} cells, {src} cells with a copy source, {} aliased cells without one (first {:?}); {yal} Y alias words", lanes.len(), nosrc.len(), &nosrc[..nosrc.len().min(12)]).unwrap();
    }
    let mut bad = Vec::new();
    let mut i = 0;
    while i < circ.ents.len() {
        let x = circ.ents[i].x;
        let mut v = [F128::ZERO; 4];
        while i < circ.ents.len() && circ.ents[i].x == x {
            let e = &circ.ents[i];
            v[e.o as usize] += e.c.mul_base(z[e.y as usize]);
            i += 1;
        }
        if !(v[0] * v[1] + v[2] + v[3]).is_zero() {
            bad.push(x);
        }
    }
    writeln!(s, "diagnose: {} violated slots; first {:?}", bad.len(), &bad[..bad.len().min(60)]).unwrap();
    // the accumulator tie (rows reading `HDR.accIn`'s `PUB` lanes 15 … 102)
    let acc = 15..15 + 2 * (crate::circuit::PHI_VARS + 1);
    let pubs: Vec<_> = circ.regs_of(Src::Pub).copied().collect();
    let mut tie: Vec<u32> = circ
        .ents
        .iter()
        .filter(|e| pubs.iter().any(|r| (r.base..r.base + r.len()).contains(&(e.y as usize)) && acc.contains(&(e.y as usize - r.base))))
        .map(|e| e.x)
        .collect();
    tie.dedup();
    let tie_bad: Vec<u32> = tie.iter().copied().filter(|x| bad.binary_search(x).is_ok()).collect();
    writeln!(s, "diagnose: accIn tie rows {}, violated {} {:?}", tie.len(), tie_bad.len(), &tie_bad[..tie_bad.len().min(10)]).unwrap();
    let show = |s: &mut String, x: u32, ind: &str| {
        for e in circ.row(x) {
            let (src, k) = circ.src_of(e.y as usize).map_or(("none".to_string(), 0), |(r, k)| (r.name().to_string(), k));
            writeln!(s, "{ind}o{} y {} c ({:#x},{:#x}) {src}[{k}] = {:#018x}", e.o, e.y, e.c.c0, e.c.c1, z[e.y as usize].0).unwrap();
        }
    };
    for &x in bad.iter().take(12) {
        writeln!(s, "slot {x} (defining rows of its OUT words):").unwrap();
        for e in circ.row(x) {
            if let Some(&r) = def.get(&e.y) {
                writeln!(s, "  word {} <- row {r}:", e.y).unwrap();
                show(&mut s, r, "    ");
            }
        }
    }
    for &x in bad.iter().take(40) {
        writeln!(s, "slot {x}:").unwrap();
        for e in circ.row(x) {
            let (src, k) = circ.src_of(e.y as usize).map_or(("none".to_string(), 0), |(r, k)| (r.name().to_string(), k));
            let pw = pow.iter().any(|p| (p.bw..p.bw + p.nb).contains(&(e.y as usize)));
            writeln!(
                s,
                "  o{} y {} c ({:#x},{:#x}) {src}[{k}] = {:#018x}{}{}{}",
                e.o,
                e.y,
                e.c.c0,
                e.c.c1,
                z[e.y as usize].0,
                def.get(&e.y).map_or(String::new(), |r| format!(" (OUT row {r})")),
                if pw { " (pow bit)" } else { "" },
                bitw.get(&e.y).map_or(String::new(), |y| format!(" (bit of {y})"))
            )
            .unwrap();
        }
    }
    s
}

/// A step of the witness: an `OUT` row with its words, or a BITS aux row (its index).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    Row(u32, Vec<u32>),
    Bits(usize),
    BOut(usize),
    /// The link's sponge row `split + i` ([`SpongeLink`]).
    Sponge(usize),
    /// A `CSUM` line.
    Csum(usize),
    /// A mini-bus read row's value ([`Readd`]).
    Readd(usize),
}

/// The defining rows with their `OUT` words (in the blob's order within a row), ordered so that every row comes
/// after the rows defining the words it reads (Kahn's algorithm, ties in the blob's order: deterministic).
/// `Err(Cycle)` if the definitions are cyclic.
pub fn solve_order(circ: &Circuit) -> Result<Vec<(u32, Vec<u32>)>, WitnessError> {
    Ok(solve_plan(circ, &[])?
        .into_iter()
        .map(|s| match s {
            Step::Row(x, ys) => (x, ys),
            _ => unreachable!(),
        })
        .collect())
}

/// [`solve_order`] with the BITS aux rows as steps too: a BITS row after the step defining its source word, a row
/// after the BITS rows defining the bit words it reads. Ties: rows in the blob's order, then the BITS rows in
/// theirs.
pub fn solve_plan(circ: &Circuit, bits: &[AuxBits]) -> Result<Vec<Step>, WitnessError> {
    solve_plan_aux(circ, Aux { bits, bout: &[], link: None, csum: &[], readd: None })
}

/// [`solve_plan`] with `BOUT` lines as steps too (after the BITS rows on ties).
pub fn solve_plan_aux(circ: &Circuit, aux: Aux) -> Result<Vec<Step>, WitnessError> {
    let (bits, bout) = (aux.bits, aux.bout);
    use std::collections::{BTreeSet, HashMap};
    let mut steps: Vec<Step> = Vec::new();
    let mut at: HashMap<u32, usize> = HashMap::new();
    let read_vals: std::collections::HashSet<u32> = aux.readd.map_or_else(Default::default, |r| r.pairs.iter().map(|p| p.1).collect());
    // a row whose OUT word is a read value keeps its relation: it defines its own W word instead (the copy rows'
    // difference word, 0 on unpadded rows and gated off on padded ones), if that word has no other definer
    let mut defined: std::collections::HashSet<u32> = circ.outs.iter().map(|o| o.1).collect();
    defined.extend(aux.bits.iter().flat_map(|b| b.dst.iter().flatten().copied()));
    defined.extend(aux.bout.iter().map(|b| b.d));
    defined.extend(aux.csum.iter().flat_map(|c| c.outputs().collect::<Vec<_>>()));
    defined.extend(read_vals.iter().copied());
    let defined = std::cell::RefCell::new(defined);
    let retarget = |x: u32, y: u32| -> Option<u32> {
        if !read_vals.contains(&y) {
            return Some(y);
        }
        let ws: Vec<u32> = circ.row(x).iter().filter(|e| e.o == 3 && e.y != y && matches!(circ.src_of(e.y as usize), Some((Src::Com, _)))).map(|e| e.y).collect();
        (ws.len() == 1 && defined.borrow_mut().insert(ws[0])).then(|| ws[0])
    };
    let outs: Vec<(u32, u32)> = circ.outs.iter().filter_map(|&(x, y)| retarget(x, y).map(|w| (x, w))).collect();
    for &(x, y) in &outs {
        let k = *at.entry(x).or_insert_with(|| {
            steps.push(Step::Row(x, Vec::new()));
            steps.len() - 1
        });
        if let Step::Row(_, ys) = &mut steps[k] {
            ys.push(y);
        }
    }
    steps.extend((0..bits.len()).map(Step::Bits));
    steps.extend((0..bout.len()).map(Step::BOut));
    let n_link = aux.link.map_or(0, |l| l.xsrc.len());
    let sp0 = steps.len();
    steps.extend((0..n_link).map(Step::Sponge));
    steps.extend((0..aux.csum.len()).map(Step::Csum));
    steps.extend((0..aux.readd.map_or(0, |r| r.pairs.len())).map(Step::Readd));
    let mut def: HashMap<u32, usize> = HashMap::new();
    for (k, st) in steps.iter().enumerate() {
        match st {
            Step::Row(_, ys) => ys.iter().for_each(|&y| assert!(def.insert(y, k).is_none(), "word {y} defined twice")),
            Step::Bits(b) => bits[*b].dst.iter().flatten().for_each(|&d| assert!(def.insert(d, k).is_none(), "word {d} defined twice")),
            Step::BOut(b) => assert!(def.insert(bout[*b].d, k).is_none(), "word {} defined twice", bout[*b].d),
            Step::Sponge(i) => {
                let l = aux.link.unwrap();
                l.xal[*i].iter().chain(&l.yal[*i]).for_each(|&(_, a)| _ = def.insert(a, k));
            }
            Step::Csum(c) => aux.csum[*c].outputs().for_each(|d| assert!(def.insert(d, k).is_none(), "word {d} defined twice")),
            Step::Readd(r) => {
                let v = aux.readd.unwrap().pairs[*r].1;
                assert!(def.insert(v, k).is_none(), "word {v} defined twice");
            }
        }
    }
    let mut indeg = vec![0usize; steps.len()];
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); steps.len()];
    for (k, st) in steps.iter().enumerate() {
        let mut deps: Vec<usize> = match st {
            Step::Row(x, _) => circ.row(*x).iter().filter_map(|e| def.get(&e.y).copied()).filter(|&d| d != k).collect(),
            Step::Bits(b) => def.get(&bits[*b].y).copied().into_iter().filter(|&d| d != k).collect(),
            Step::BOut(b) => def.get(&bout[*b].y).copied().into_iter().filter(|&d| d != k).collect(),
            Step::Sponge(i) => {
                let l = aux.link.unwrap();
                let r = r3core::layout::SPLIT + i;
                let mut d: Vec<usize> = l.xsrc[*i].iter().flatten().filter_map(|c| def.get(c).copied()).collect();
                if *i > 0 && l.cont[r] {
                    d.push(sp0 + i - 1);
                }
                d.retain(|&x| x != k);
                d
            }
            Step::Csum(c) => aux.csum[*c].bd.iter().filter_map(|b| def.get(b).copied()).filter(|&d| d != k).collect(),
            Step::Readd(r) => def.get(&aux.readd.unwrap().pairs[*r].0).copied().into_iter().filter(|&d| d != k).collect(),
        };
        deps.sort_unstable();
        deps.dedup();
        indeg[k] = deps.len();
        for d in deps {
            users[d].push(k);
        }
    }
    // ready steps by position (rows in blob order first, then BITS rows)
    let mut ready: BTreeSet<usize> = (0..steps.len()).filter(|&k| indeg[k] == 0).collect();
    let mut order = Vec::with_capacity(steps.len());
    while let Some(k) = ready.pop_first() {
        order.push(k);
        for &u in &users[k] {
            indeg[u] -= 1;
            if indeg[u] == 0 {
                ready.insert(u);
            }
        }
    }
    if order.len() != steps.len() {
        return Err(WitnessError::Cycle);
    }
    let mut steps: Vec<Option<Step>> = steps.into_iter().map(Some).collect();
    Ok(order.into_iter().map(|k| steps[k].take().unwrap()).collect())
}

/// `Σ_i c_i·y_i = v` with `y_i ∈ K`: one unknown (`v/c_0` must be in `K`) or two (a 2×2 system over `K` on the
/// coordinates `c₀ + c₁·y`; `c_0`, `c_1` must be `K`-independent).
pub fn solve_k(c: &[F128], v: F128) -> Option<Vec<F64>> {
    match c {
        [c0] => (v * c0.inv()).as_base().map(|k| vec![k]),
        [ca, cb] => {
            let (a0, a1, b0, b1, v0, v1) = (F64(ca.c0), F64(ca.c1), F64(cb.c0), F64(cb.c1), F64(v.c0), F64(v.c1));
            let det = a0 * b1 + a1 * b0;
            if det.is_zero() {
                return None;
            }
            let di = det.inv();
            Some(vec![(v0 * b1 + v1 * b0) * di, (a0 * v1 + a1 * v0) * di])
        }
        _ => None,
    }
}

/// `(M_o z)(x)` for `o < 4`, every slot (`2^20` values each).
pub fn mat_z(circ: &Circuit, z: &[F64]) -> [Vec<F128>; 4] {
    let mut m: [Vec<F128>; 4] = std::array::from_fn(|_| vec![F128::ZERO; 1 << X_VARS]);
    for e in &circ.ents {
        m[e.o as usize][e.x as usize] += e.c.mul_base(z[e.y as usize]);
    }
    m
}

/// The first slot where `A·B + C ≠ 0` (Lean `WiringRelE`), if any.
pub fn first_violation(circ: &Circuit, z: &[F64]) -> Option<u32> {
    let mut i = 0;
    while i < circ.ents.len() {
        let x = circ.ents[i].x;
        let mut v = [F128::ZERO; 4];
        while i < circ.ents.len() && circ.ents[i].x == x {
            let e = &circ.ents[i];
            v[e.o as usize] += e.c.mul_base(z[e.y as usize]);
            i += 1;
        }
        if !(v[0] * v[1] + v[2] + v[3]).is_zero() {
            return Some(x);
        }
    }
    None
}

/// What [`acc_tie_probe`] found.
#[derive(Debug)]
pub struct TieProbe {
    /// Rows reading a `PUB` word of `HDR.accIn` (lanes 15 … 102): the circuit's accumulator tie (CD's `qacc6`).
    pub tie_rows: usize,
    /// The witness on the honest header.
    pub honest: Result<(), WitnessError>,
    /// The witness with `accIn.pt[0]` and with `accIn.y` altered (one lane bit each).
    pub tampered: [Result<(), WitnessError>; 2],
}

/// Dev: the accumulator tie on a node stack (`b = 1`): the rows that read `accIn`, the witness on `hdr`, and on
/// `hdr` with `accIn` altered (a node whose `accIn` is not the child's `accOut` must have no witness). Works on
/// copies of the stack.
pub fn acc_tie_probe(circ: &Circuit, stack: &[F64], hdr: &[u8]) -> TieProbe {
    const ACC_LANES: std::ops::Range<usize> = 15..15 + 2 * (crate::circuit::PHI_VARS + 1);
    let pub_regs: Vec<_> = circ.regs_of(Src::Pub).copied().collect();
    let reads_acc = |y: usize| pub_regs.iter().any(|r| (r.base..r.base + r.len()).contains(&y) && ACC_LANES.contains(&(y - r.base)));
    let mut rows: Vec<u32> = circ.ents.iter().filter(|e| reads_acc(e.y as usize)).map(|e| e.x).collect();
    rows.dedup();
    let run = |h: &[u8]| {
        let mut s = stack.to_vec();
        witness(circ, &mut s, &pub_lanes(h)).map(|_| ())
    };
    let honest = run(hdr);
    let tamper = |lane: usize| {
        let mut h = hdr.to_vec();
        h[8 * lane] ^= 1;
        run(&h)
    };
    TieProbe { tie_rows: rows.len(), honest, tampered: [tamper(ACC_LANES.start), tamper(ACC_LANES.end - 2)] }
}
