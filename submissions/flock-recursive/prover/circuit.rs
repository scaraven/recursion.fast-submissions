//! The leaf chain block (blueprint §4.1, P1 layout `params.rs`): leanerVM's BLAKE2s product
//! circuit (`LeanerVM/Protocol/Blake2sCircuit.lean` and `Protocol/ToArkLib/Flock/{Words,Builder,
//! Circuit}.lean`, leanerVM `532ebb4`, Apache-2.0, `../LICENSE-leanerVM`; itself a transcription of
//! leanVM `crates/flock/src/hash.rs`, pin `a386121f`), as `submissions/spartan-srom/prover/circuit.rs`
//! builds it, with the chain step's constants and the P1 re-based layout:
//!
//! * `h0` at 0…255 and every constant message/counter/flag bit as constant rows: `(one, one)` for a
//!   1 bit, the zero row for a 0 bit;
//! * the output digest at 256…511 (rows `(out form, one)`);
//! * the message at 512…1023 (A.6): the input digest `d` (bytes 1…32) at 520…775 (input rows
//!   `(var k, one)`), the tag byte 0x43 at 512…519, zero bytes 776…1023;
//! * counter and flags at 1024…1151, the constant one at 1152 with the **zero row**: the batch
//!   constraint is `(Az)∘(Bz) = z + e`, `e` the indicator of position 1152 in every block, which
//!   forces `z_1152 = 1` (P1 choice in place of rev. 2's public-pattern claim; P1-RESULT §4);
//! * the 14,720 gates from 1280.
//!
//! The gadget program is run once into a *tape*: a form (an `F₂`-linear combination of block
//! positions) is a node of an XOR DAG whose leaves are positions. One tape serves the bit trace
//! (`trace`, `trace64`: the witness `z` and its rows `Az`, `Bz`) and the transpose walk over F
//! (`transpose`: `Σ_k e_A(k) A0(k, ·) + e_B(k) B0(k, ·)`, the lincheck's column marginal).

use crate::blake2s::{IV, SIGMA};
use crate::field::F;
pub use crate::params::{BLOCK_LOG, D_BASE as MSG_IN, F0_BASE, F1_BASE, GATE_BASE, MSG_BASE, ONE_POS as CPOS, OUT_BASE as OUT, THI_BASE, TLO_BASE};

pub const BLOCK: usize = 1 << BLOCK_LOG;

/// The position of message bit `b`: `MSG_BASE + b` (A.6, natural order).
pub fn msg_pos(b: usize) -> usize {
    MSG_BASE + b
}

/// Node kinds. A node's value is a form; `Gate` is the variable of the gate's position.
#[derive(Clone, Copy, Debug)]
pub enum Node {
    Zero,
    Var(u32),
    Xor(u32, u32),
    /// The gate at position `p` with forms `a`, `b`; as a form it is `var p`.
    Gate(u32, u32, u32),
}

type Word = [u32; 32];

struct Builder {
    nodes: Vec<Node>,
    var_of: Vec<u32>, // position -> Var node (0 = none)
    next: usize,
    gates: Vec<(usize, u32, u32)>,
}

impl Builder {
    fn xor(&mut self, a: u32, b: u32) -> u32 {
        if a == 0 {
            return b;
        }
        if b == 0 {
            return a;
        }
        self.nodes.push(Node::Xor(a, b));
        (self.nodes.len() - 1) as u32
    }
    fn var(&mut self, p: usize) -> u32 {
        let p = p % BLOCK; // `pos` reduces modulo the block size
        if self.var_of[p] == 0 {
            self.nodes.push(Node::Var(p as u32));
            self.var_of[p] = (self.nodes.len() - 1) as u32;
        }
        self.var_of[p]
    }
    fn gate_at(&mut self, p: usize, a: u32, b: u32) -> u32 {
        self.nodes.push(Node::Gate(p as u32, a, b));
        self.gates.push((p, a, b));
        (self.nodes.len() - 1) as u32
    }
    /// `mul`: the gate `(a, b)` at the next position.
    fn mul(&mut self, a: u32, b: u32) -> u32 {
        let p = self.next;
        self.next += 1;
        self.gate_at(p % BLOCK, a, b)
    }
    fn xor_w(&mut self, x: &Word, y: &Word) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            o[i] = self.xor(x[i], y[i]);
        }
        o
    }
    fn rotr_w(w: &Word, n: usize) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            o[i] = w[(i + n) % 32];
        }
        o
    }
    fn lit_w(&mut self, c: u32) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            if (c >> i) & 1 == 1 {
                o[i] = self.var(CPOS);
            }
        }
        o
    }
    fn in_w(&mut self, b: usize) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            o[i] = self.var(b + i);
        }
        o
    }
    /// `addCarries x y 31 0`: carries `c_0 = 0, …, c_31`, one gate per carry into bits `1 … 31`.
    fn add_carries(&mut self, x: &Word, y: &Word) -> Vec<u32> {
        let mut cs = Vec::with_capacity(32);
        let mut c = 0;
        for i in 0..31 {
            let a = self.xor(x[i], c);
            let b = self.xor(y[i], c);
            let g = self.mul(a, b);
            cs.push(c);
            c = self.xor(c, g);
        }
        cs.push(c);
        cs
    }
    /// `sumW p q cs`: bit `i` is `p_i + q_i + c_i`.
    fn sum_w(&mut self, p: &Word, q: &Word, cs: &[u32]) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            let pq = self.xor(p[i], q[i]);
            o[i] = self.xor(pq, cs.get(i).copied().unwrap_or(0));
        }
        o
    }
    fn add_w(&mut self, x: &Word, y: &Word) -> Word {
        let cs = self.add_carries(x, y);
        self.sum_w(x, y, &cs)
    }
    /// `add3W x y z`: 31 majority gates, then 30 ripple gates.
    fn add3_w(&mut self, x: &Word, y: &Word, z: &Word) -> Word {
        // majorities x y z 31
        let mut ms = Vec::with_capacity(31);
        for i in 0..31 {
            let a = self.xor(x[i], z[i]);
            let b = self.xor(y[i], z[i]);
            let g = self.mul(a, b);
            ms.push(self.xor(g, z[i]));
        }
        // xor3W x y z
        let mut p = [0; 32];
        for i in 0..32 {
            let xy = self.xor(x[i], y[i]);
            p[i] = self.xor(xy, z[i]);
        }
        // shiftW ms
        let mut q = [0; 32];
        for i in 1..32 {
            q[i] = ms[i - 1];
        }
        // rippleCarries p q 31 0
        let mut cs = Vec::with_capacity(32);
        let mut c = 0;
        for i in 0..31 {
            if i >= 1 {
                let a = self.xor(p[i], c);
                let b = self.xor(q[i], c);
                let g = self.mul(a, b);
                cs.push(c);
                c = self.xor(c, g);
            } else {
                cs.push(c);
            }
        }
        cs.push(c);
        self.sum_w(&p, &q, &cs)
    }
    #[allow(clippy::too_many_arguments)]
    fn g_w(&mut self, v: &mut [Word; 16], a: usize, b: usize, c: usize, d: usize, mx: &Word, my: &Word) {
        let a1 = self.add3_w(&v[a], &v[b], mx);
        let t = self.xor_w(&v[d], &a1);
        let d1 = Self::rotr_w(&t, 16);
        let c1 = self.add_w(&v[c], &d1);
        let t = self.xor_w(&v[b], &c1);
        let b1 = Self::rotr_w(&t, 12);
        let a2 = self.add3_w(&a1, &b1, my);
        let t = self.xor_w(&d1, &a2);
        let d2 = Self::rotr_w(&t, 8);
        let c2 = self.add_w(&c1, &d2);
        let t = self.xor_w(&b1, &c2);
        let b2 = Self::rotr_w(&t, 7);
        v[a] = a2;
        v[b] = b2;
        v[c] = c2;
        v[d] = d2;
    }
}

/// The chain block circuit as a tape plus the row of every position.
pub struct Circuit {
    pub nodes: Vec<Node>,
    /// `rows[k] = Some((a, b))`, or `None` for the zero row `(0, 0)`.
    pub rows: Vec<Option<(u32, u32)>>,
    /// The gates in evaluation order (`chainBlock.gates`): constant rows, compression gates,
    /// output rows.
    pub gates: Vec<(usize, u32, u32)>,
    pub v512: u32,
}

/// The constant bit of a constant position of the leaf block, or `None` if `k` is not one:
/// `h0` at 0…255, the tag byte 0x43 (message byte 0) and the zero message bytes 33…63, the counter
/// `t = 33` at `TLO_BASE`, `t_hi = 0`, `f0 = 0xFFFFFFFF`, `f1 = 0`.
pub fn const_bit(k: usize) -> Option<bool> {
    let h0 = crate::blake2s::h0();
    if k < 256 {
        return Some((h0[k / 32] >> (k % 32)) & 1 == 1);
    }
    if (MSG_BASE..MSG_BASE + 512).contains(&k) {
        let byte = (k - MSG_BASE) / 8;
        let bit = (k - MSG_BASE) % 8;
        return match byte {
            0 => Some((0x43u32 >> bit) & 1 == 1),
            33..=63 => Some(false),
            _ => None,
        };
    }
    match k {
        _ if (TLO_BASE..TLO_BASE + 32).contains(&k) => Some((33u32 >> (k - TLO_BASE)) & 1 == 1),
        _ if (THI_BASE..THI_BASE + 32).contains(&k) => Some(false),
        _ if (F0_BASE..F0_BASE + 32).contains(&k) => Some(true),
        _ if (F1_BASE..F1_BASE + 32).contains(&k) => Some(false),
        _ => None,
    }
}

/// Transpose a 64 × 64 bit matrix in place: bit `j` of `a[i]` becomes bit `i` of `a[j]` (each
/// stage swaps the off-diagonal `w × w` blocks).
pub fn transpose64(a: &mut [u64; 64]) {
    const M: [u64; 6] = [
        0x0000_0000_FFFF_FFFF,
        0x0000_FFFF_0000_FFFF,
        0x00FF_00FF_00FF_00FF,
        0x0F0F_0F0F_0F0F_0F0F,
        0x3333_3333_3333_3333,
        0x5555_5555_5555_5555,
    ];
    for (s, &m) in M.iter().enumerate() {
        let w = 32 >> s;
        for i in 0..64 {
            if i & w == 0 {
                let t = ((a[i] >> w) ^ a[i + w]) & m;
                a[i + w] ^= t;
                a[i] ^= t << w;
            }
        }
    }
}

impl Circuit {
    /// The leaf chain block.
    pub fn build() -> Circuit {
        let mut b = Builder { nodes: vec![Node::Zero], var_of: vec![0; BLOCK], next: GATE_BASE, gates: vec![] };
        let v512 = b.var(CPOS);
        // the constant rows, prepended to the gates, ascending position: `(one, one)` for a 1
        // bit, `(0, 0)` for a 0 bit
        for k in 0..GATE_BASE {
            match const_bit(k) {
                Some(true) => {
                    b.gate_at(k, v512, v512);
                }
                Some(false) => {
                    b.gate_at(k, 0, 0);
                }
                None => {}
            }
        }
        // compressW
        let mut v: [Word; 16] = [[0; 32]; 16];
        let cnt = [TLO_BASE, THI_BASE, F0_BASE, F1_BASE];
        for w in 0..16 {
            v[w] = if w < 8 {
                b.in_w(32 * w)
            } else if w < 12 {
                b.lit_w(IV[w - 8])
            } else {
                let l = b.lit_w(IV[w - 8]);
                let inp = b.in_w(cnt[w - 12]);
                b.xor_w(&l, &inp)
            };
        }
        let mut msg: [Word; 16] = [[0; 32]; 16];
        for w in 0..16 {
            for i in 0..32 {
                msg[w][i] = b.var(msg_pos(32 * w + i));
            }
        }
        for s in SIGMA.iter() {
            b.g_w(&mut v, 0, 4, 8, 12, &msg[s[0]], &msg[s[1]]);
            b.g_w(&mut v, 1, 5, 9, 13, &msg[s[2]], &msg[s[3]]);
            b.g_w(&mut v, 2, 6, 10, 14, &msg[s[4]], &msg[s[5]]);
            b.g_w(&mut v, 3, 7, 11, 15, &msg[s[6]], &msg[s[7]]);
            b.g_w(&mut v, 0, 5, 10, 15, &msg[s[8]], &msg[s[9]]);
            b.g_w(&mut v, 1, 6, 11, 12, &msg[s[10]], &msg[s[11]]);
            b.g_w(&mut v, 2, 7, 8, 13, &msg[s[12]], &msg[s[13]]);
            b.g_w(&mut v, 3, 4, 9, 14, &msg[s[14]], &msg[s[15]]);
        }
        assert_eq!(b.next, GATE_BASE + crate::params::GATES, "80 G steps x 184 gates");
        let mut outs = [[0u32; 32]; 8];
        for w in 0..8 {
            let t = b.xor_w(&v[w], &v[w + 8]);
            let cv = b.in_w(32 * w);
            outs[w] = b.xor_w(&t, &cv);
        }
        // output rows (out bit, one)
        for w in 0..8 {
            for i in 0..32 {
                b.gate_at(OUT + 32 * w + i, outs[w][i], v512);
            }
        }
        // rows: gates first (first occurrence), then the inputs; the one position and every
        // other position have the zero row
        let mut rows: Vec<Option<(u32, u32)>> = vec![None; BLOCK];
        let mut is_gate = vec![false; BLOCK];
        for &(p, a, bb) in &b.gates {
            if !is_gate[p] {
                is_gate[p] = true;
                rows[p] = Some((a, bb));
            }
        }
        assert!(!is_gate[CPOS]);
        for k in MSG_IN..MSG_IN + 256 {
            assert!(!is_gate[k]);
            let vk = b.var(k);
            rows[k] = Some((vk, v512));
        }
        Circuit { nodes: b.nodes, rows, gates: b.gates, v512 }
    }

    /// The honest block for the message digest `d` (`chainTrace d`): returns the bits of the
    /// block `z` and of the rows' forms `Az`, `Bz` (each `2^14` bits as 256 words). Row 512 of
    /// the chain R1CS (`A = B = pub(0) = 1`) agrees with the constant row here.
    pub fn trace(&self, d: &[u8; 32], vals: &mut Vec<u8>) -> ([u64; 256], [u64; 256], [u64; 256]) {
        let mut z = vec![0u8; BLOCK];
        z[CPOS] = 1;
        for e in 0..32 {
            for bit in 0..8 {
                z[msg_pos(8 * (e + 1) + bit)] = (d[e] >> bit) & 1;
            }
        }
        vals.clear();
        vals.resize(self.nodes.len(), 0);
        for (i, nd) in self.nodes.iter().enumerate() {
            vals[i] = match *nd {
                Node::Zero => 0,
                Node::Var(p) => z[p as usize],
                Node::Xor(a, b) => vals[a as usize] ^ vals[b as usize],
                Node::Gate(p, a, b) => {
                    let v = vals[a as usize] & vals[b as usize];
                    z[p as usize] = v;
                    v
                }
            };
        }
        let mut zw = [0u64; 256];
        let mut aw = [0u64; 256];
        let mut bw = [0u64; 256];
        for k in 0..BLOCK {
            zw[k / 64] |= (z[k] as u64) << (k % 64);
            if let Some((a, b)) = self.rows[k] {
                aw[k / 64] |= (vals[a as usize] as u64) << (k % 64);
                bw[k / 64] |= (vals[b as usize] as u64) << (k % 64);
            }
        }
        (zw, aw, bw)
    }

    /// `trace` of up to 64 blocks at once, bit-sliced (lane `t` of every word is block `t`): the
    /// same node program on `u64` lanes, then 64 × 64 bit transposes. Block `t`'s `z`, `Az`, `Bz`
    /// words go to `zw`, `aw`, `bw` at `[256 t, 256 t + 256)`.
    pub fn trace64(&self, ds: &[[u8; 32]], vals: &mut Vec<u64>, zw: &mut [u64], aw: &mut [u64], bw: &mut [u64]) {
        let k = ds.len();
        assert!(k <= 64 && zw.len() == 256 * k && aw.len() == 256 * k && bw.len() == 256 * k);
        let mut z = vec![0u64; BLOCK];
        z[CPOS] = if k == 64 { !0 } else { (1u64 << k) - 1 };
        for e in 0..32 {
            for bit in 0..8 {
                let mut m = 0u64;
                for (t, d) in ds.iter().enumerate() {
                    m |= (((d[e] >> bit) & 1) as u64) << t;
                }
                z[msg_pos(8 * (e + 1) + bit)] = m;
            }
        }
        vals.clear();
        vals.resize(self.nodes.len(), 0);
        for (i, nd) in self.nodes.iter().enumerate() {
            vals[i] = match *nd {
                Node::Zero => 0,
                Node::Var(p) => z[p as usize],
                Node::Xor(a, b) => vals[a as usize] ^ vals[b as usize],
                Node::Gate(p, a, b) => {
                    let v = vals[a as usize] & vals[b as usize];
                    z[p as usize] = v;
                    v
                }
            };
        }
        let (mut mz, mut ma, mut mb) = ([0u64; 64], [0u64; 64], [0u64; 64]);
        for wi in 0..BLOCK / 64 {
            for j in 0..64 {
                let p = 64 * wi + j;
                mz[j] = z[p];
                (ma[j], mb[j]) = match self.rows[p] {
                    Some((a, b)) => (vals[a as usize], vals[b as usize]),
                    None => (0, 0),
                };
            }
            transpose64(&mut mz);
            transpose64(&mut ma);
            transpose64(&mut mb);
            for t in 0..k {
                zw[256 * t + wi] = mz[t];
                aw[256 * t + wi] = ma[t];
                bw[256 * t + wi] = mb[t];
            }
        }
    }

    /// Node values over F with `var j ↦ wt(j)`.
    fn values(&self, wt: &[F]) -> Vec<F> {
        let mut val = vec![F::ZERO; self.nodes.len()];
        for (i, nd) in self.nodes.iter().enumerate() {
            val[i] = match *nd {
                Node::Zero => F::ZERO,
                Node::Var(p) | Node::Gate(p, _, _) => wt[p as usize],
                Node::Xor(a, b) => val[a as usize] + val[b as usize],
            };
        }
        val
    }

    /// The forward walk: `(Σ_k e(k) Σ_j A0(k,j) wt(j), same for B0)` (tests).
    pub fn walk(&self, e: &[F], wt: &[F]) -> (F, F) {
        let val = self.values(wt);
        let mut a_acc = F::ZERO;
        let mut b_acc = F::ZERO;
        for k in 0..BLOCK {
            if let Some((a, b)) = self.rows[k] {
                a_acc += e[k] * val[a as usize];
                b_acc += e[k] * val[b as usize];
            }
        }
        (a_acc, b_acc)
    }

    /// The transpose walk: `u(j) = Σ_k ea(k) A0(k, j) + eb(k) B0(k, j)`.
    pub fn transpose(&self, ea: &[F], eb: &[F]) -> Vec<F> {
        let mut adj = vec![F::ZERO; self.nodes.len()];
        for k in 0..BLOCK {
            if let Some((a, b)) = self.rows[k] {
                adj[a as usize] += ea[k];
                adj[b as usize] += eb[k];
            }
        }
        let mut u = vec![F::ZERO; BLOCK];
        for i in (1..self.nodes.len()).rev() {
            let g = adj[i];
            if g.is_zero() {
                continue;
            }
            match self.nodes[i] {
                Node::Zero => {}
                Node::Var(p) | Node::Gate(p, _, _) => u[p as usize] += g,
                Node::Xor(a, b) => {
                    adj[a as usize] += g;
                    adj[b as usize] += g;
                }
            }
        }
        u
    }

    /// The rows of `rowOf` as bitsets (`2^14` bits, 256 words each): `(a, b)` per position.
    pub fn row_bitsets(&self) -> Vec<([u64; 256], [u64; 256])> {
        let mut val: Vec<Box<[u64; 256]>> = Vec::with_capacity(self.nodes.len());
        for nd in self.nodes.iter() {
            let mut v = Box::new([0u64; 256]);
            match *nd {
                Node::Zero => {}
                Node::Var(p) | Node::Gate(p, _, _) => v[p as usize / 64] |= 1u64 << (p % 64),
                Node::Xor(a, b) => {
                    for w in 0..256 {
                        v[w] = val[a as usize][w] ^ val[b as usize][w];
                    }
                }
            }
            val.push(v);
        }
        (0..BLOCK)
            .map(|k| match self.rows[k] {
                Some((a, b)) => (*val[a as usize], *val[b as usize]),
                None => ([0u64; 256], [0u64; 256]),
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blake2s::chain_step;
    use crate::mle::eq_table;

    #[test]
    fn transpose64_is_the_transpose() {
        let mut s = 0x9E37_79B9_7F4A_7C15u64;
        let a: [u64; 64] = std::array::from_fn(|_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        });
        let mut t = a;
        transpose64(&mut t);
        for i in 0..64 {
            for j in 0..64 {
                assert_eq!((t[i] >> j) & 1, (a[j] >> i) & 1);
            }
        }
    }

    #[test]
    fn trace64_equals_trace() {
        let c = Circuit::build();
        let (mut v8, mut v64) = (vec![], vec![]);
        for k in [64usize, 5] {
            let ds: Vec<[u8; 32]> = (0..k).map(|t| std::array::from_fn(|i| (i as u8 ^ t as u8).wrapping_mul(29).wrapping_add(k as u8))).collect();
            let (mut zw, mut aw, mut bw) = (vec![0u64; 256 * k], vec![0u64; 256 * k], vec![0u64; 256 * k]);
            c.trace64(&ds, &mut v64, &mut zw, &mut aw, &mut bw);
            for (t, d) in ds.iter().enumerate() {
                let (z, a, b) = c.trace(d, &mut v8);
                assert_eq!(&zw[256 * t..256 * t + 256], &z[..]);
                assert_eq!(&aw[256 * t..256 * t + 256], &a[..]);
                assert_eq!(&bw[256 * t..256 * t + 256], &b[..]);
            }
        }
    }

    /// The block computes the chain step: output at 256…511, input at 512…767, and every row
    /// satisfies `a ∧ b = z ⊕ e` (`e` = the one position).
    #[test]
    fn trace_computes_chain_step_and_satisfies_rows() {
        let c = Circuit::build();
        let mut vals = vec![];
        for seed in 0..4u8 {
            let d: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(seed.wrapping_mul(91)));
            let (z, a, b) = c.trace(&d, &mut vals);
            let out = chain_step(&d);
            for e in 0..32 {
                for bit in 0..8 {
                    let k = OUT + 8 * e + bit;
                    assert_eq!((z[k / 64] >> (k % 64)) & 1, ((out[e] >> bit) & 1) as u64);
                    let k = MSG_IN + 8 * e + bit;
                    assert_eq!((z[k / 64] >> (k % 64)) & 1, ((d[e] >> bit) & 1) as u64);
                }
            }
            for w in 0..256 {
                let e = if w == CPOS / 64 { 1u64 << (CPOS % 64) } else { 0 };
                assert_eq!(a[w] & b[w], z[w] ^ e, "row word {w}");
            }
            assert!(z[GATE_BASE / 64..].iter().any(|&x| x != 0));
        }
    }

    #[test]
    fn transpose_is_adjoint_of_walk() {
        let c = Circuit::build();
        let mut s = 99u64;
        let mut nx = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        };
        let rk: Vec<F> = (0..14).map(|_| F::new(nx(), nx())).collect();
        let rj: Vec<F> = (0..14).map(|_| F::new(nx(), nx())).collect();
        let e = eq_table(&rk);
        let wt = eq_table(&rj);
        let (wa, wb) = c.walk(&e, &wt);
        let rho = F::new(nx(), nx());
        let eb: Vec<F> = e.iter().map(|&x| x * rho).collect();
        let u = c.transpose(&e, &eb);
        let mut dot = F::ZERO;
        for j in 0..BLOCK {
            dot += u[j] * wt[j];
        }
        assert_eq!(dot, wa + rho * wb);
    }
}
