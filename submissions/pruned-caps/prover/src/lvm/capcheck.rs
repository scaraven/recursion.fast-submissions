//! CAP (stage S2GB, dev): the prover's V twin of the S2GB opening structure on a signed file (`lvm-prover capcheck
//! FILE…`, `LVM_STAGE=S2GB`). The oracle's answers are taken from the trace as given; everything else is checked against
//! `π`: every FS query is `st ‖ pending` (the bytes transmitted since the last one; positions queries after the first
//! `st`), every leaf query is its row, every path query `cur ‖ sib` / `sib ‖ cur` by the position's bit, the layer
//! `L[x]` (first path's top, else the next tail node, ascending `x`), every path top `= L[q >> D]`, the heap queries
//! `A[2k] ‖ A[2k+1]` for `k = 2^m − 1` down to `2^s`, `A[2^s + i]` = the sent node `i`, then body cursor `= piStatic`
//! and tail cursor `= |π|`. Not checked: the answers themselves, the sumchecks, the signature (`V_S` does those).

use crate::format::Signed;
use crate::lvm::params::{self, Item, Params, E_BYTES, NODE_BYTES, POSITIONS_PER_ANSWER};

/// `Ok(|X| per opening)` or the first violation.
pub fn check(p: &Params, f: &Signed) -> Result<Vec<usize>, String> {
    let pi = &f.pi;
    let tr = &f.tr;
    if tr.len() != params::query_list(p).len() {
        return Err(format!("qS {} != {}", tr.len(), params::query_list(p).len()));
    }
    let stat = params::pi_size(p);
    if pi.len() < stat || pi.len() > stat + params::pi_tail_max(p) {
        return Err(format!("|pi| {} outside [{stat}, {}]", pi.len(), stat + params::pi_tail_max(p)));
    }
    let hb = params::header_bytes(p);
    let mut off = hb;
    let mut pend = hb;
    let mut tail = stat;
    let mut ti = 2usize;
    let mut st = tr[1].1;
    let mut sent: Vec<Vec<[u8; 32]>> = vec![Vec::new(); p.main_levels.len()];
    let mut positions: Vec<usize> = Vec::new();
    let mut covered = Vec::new();
    let fs = |ti: usize, st: &[u8; 32], body: &[u8]| -> Result<[u8; 32], String> {
        let (q, a) = &tr[ti];
        if q.len() != 32 + body.len() || &q[..32] != st || &q[32..] != body {
            return Err(format!("FS query {ti}: not st ‖ pending ({} B)", body.len()));
        }
        Ok(*a)
    };
    for it in params::schedule(p) {
        match it {
            Item::Read(m) => off += E_BYTES * m,
            Item::Read16(m) => off += 16 * m,
            Item::Nonce => off += 8,
            Item::Cap(c, _, lv) => {
                sent[lv] = (0..1usize << c).map(|i| pi[off + 32 * i..off + 32 * i + 32].try_into().unwrap()).collect();
                off += NODE_BYTES << c;
            }
            Item::Sample => {
                st = fs(ti, &st, &pi[pend..off])?;
                ti += 1;
                pend = off;
            }
            Item::Positions(com, lv) => {
                let l = p.levels(com)[lv];
                let d = l.height;
                positions.clear();
                for j in 0..l.t.div_ceil(POSITIONS_PER_ANSWER) {
                    st = fs(ti, &st, if j == 0 { &pi[pend..off] } else { &[] })?;
                    ti += 1;
                    pend = off;
                    let lane = |k: usize| u64::from_le_bytes(st[8 * k..8 * k + 8].try_into().unwrap());
                    let v = (lane(0) as u128) | ((lane(1) as u128) << 64);
                    for i in 0..POSITIONS_PER_ANSWER.min(l.t - positions.len()) {
                        let o = i * d;
                        let c = if o + d <= 128 {
                            (v >> o) as u64
                        } else if o >= 128 {
                            lane(2) >> (o - 128)
                        } else {
                            ((v >> o) as u64) | (lane(2) << (128 - o))
                        };
                        positions.push((c & ((1u64 << d) - 1)) as usize);
                    }
                }
            }
            Item::Opening(com, lv) => {
                let l = p.levels(com)[lv];
                let (m, dd) = (l.cap, l.path);
                let mut tops = Vec::with_capacity(l.t);
                for &q in &positions {
                    let (lq, la) = &tr[ti];
                    if lq.len() != l.row || lq[..] != pi[off..off + l.row] {
                        return Err(format!("leaf query {ti} (opening {lv}) is not its row in pi"));
                    }
                    off += l.row;
                    ti += 1;
                    let mut cur = *la;
                    for j in 0..dd {
                        let sib = &pi[off..off + 32];
                        off += 32;
                        let (nq, na) = &tr[ti];
                        let want = if (q >> j) & 1 == 0 { [&cur[..], sib].concat() } else { [sib, &cur[..]].concat() };
                        if nq[..] != want[..] {
                            return Err(format!("node query {ti} (opening {lv}, position {q}, level {j}) is not cur/sib"));
                        }
                        cur = *na;
                        ti += 1;
                    }
                    tops.push((q >> dd, cur));
                }
                // (opened rows and siblings are never absorbed: the driver's `pend := off`)
                pend = off;
                if !params::FrontCfg::get().cappr {
                    let cap = &sent[lv];
                    if let Some((x, _)) = tops.iter().find(|(x, t)| cap[*x] != *t) {
                        return Err(format!("opening {lv}: a path does not end at cap node {x}"));
                    }
                    continue;
                }
                let s = sent[lv].len().trailing_zeros() as usize;
                let mut layer: Vec<Option<[u8; 32]>> = vec![None; 1 << m];
                for (x, t) in &tops {
                    layer[*x].get_or_insert(*t);
                }
                if let Some((x, _)) = tops.iter().find(|(x, t)| layer[*x] != Some(*t)) {
                    return Err(format!("opening {lv}: a path's top is not L[{x}] (the first path's)"));
                }
                covered.push(layer.iter().filter(|x| x.is_some()).count());
                let mut a = vec![[0u8; 32]; 2 << m];
                for (x, n) in layer.iter().enumerate() {
                    a[(1 << m) + x] = match n {
                        Some(t) => *t,
                        None => {
                            if tail + 32 > pi.len() {
                                return Err(format!("opening {lv}: the tail ends before L[{x}]"));
                            }
                            tail += 32;
                            pi[tail - 32..tail].try_into().unwrap()
                        }
                    };
                }
                for k in ((1usize << s)..(1 << m)).rev() {
                    let (hq, ha) = &tr[ti];
                    if hq[..] != [&a[2 * k][..], &a[2 * k + 1][..]].concat()[..] {
                        return Err(format!("heap query {ti} (opening {lv}, k = {k}) is not A[2k] ‖ A[2k+1]"));
                    }
                    a[k] = *ha;
                    ti += 1;
                }
                if a[1 << s..2 << s] != sent[lv][..] {
                    return Err(format!("opening {lv}: the heap does not end at the sent nodes (2^{s})"));
                }
            }
        }
    }
    if off != stat {
        return Err(format!("body cursor {off} != piStatic {stat}"));
    }
    if tail != pi.len() {
        return Err(format!("tail cursor {tail} != |pi| {}", pi.len()));
    }
    if ti != tr.len() {
        return Err(format!("trace cursor {ti} != qS {}", tr.len()));
    }
    Ok(covered)
}
