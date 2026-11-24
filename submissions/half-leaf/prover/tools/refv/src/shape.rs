//! The `Shape` `V_S` runs at. `P18` is `fs6::params::P18` (RT's literal of `params6.json`, itself checked against
//! the JSON); `refv` only lifts it to a level list of any length, so that a small test shape `T15` (three levels,
//! the same code paths: a `K`-leaf level, an `E`-leaf level, the final level) runs in milliseconds.

pub use fs6::params::Level;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    pub name: &'static str,
    /// `log2 N★`: the header's `n` must be `2^log_blocks`.
    pub log_blocks: u32,
    /// Stack variables `M`.
    pub stack_log: usize,
    /// Occupied level-0 lanes (slots `0 … lanes−1`).
    pub lanes: usize,
    /// `v = phiVars` (`|HDR| = 136 + 16v`, FORMAT6 v2.2). Not frozen (§T); `fs6`'s provisional value.
    pub phi_vars: usize,
    pub levels: Vec<Level>,
    pub grind_batch: u32,
    pub final_coeffs: usize,
    pub tail_rounds: usize,
    pub grind_tail: u32,
    pub j0: usize,
    pub qv: usize,
}

impl Shape {
    /// FORMAT6 §3 per `Shape`: no chain query may have a node's (64) or a leaf's length.
    pub fn forbidden_lengths(&self) -> Vec<usize> {
        let mut v = vec![64];
        for l in &self.levels {
            if !v.contains(&l.leaf_bytes) {
                v.push(l.leaf_bytes);
            }
        }
        v
    }

    pub fn hdr_len(&self) -> usize {
        136 + 16 * self.phi_vars
    }

    /// The structural identities every shape must satisfy (a `refv` bug if not).
    pub fn check(&self) {
        let l = &self.levels;
        assert!(l.len() >= 2, "a non-final level and the final one");
        assert_eq!(l[0].fold, 6, "level 0 folds the 64 lanes of a stack row");
        assert!(self.lanes <= 64);
        assert_eq!(l[0].leaf_bytes, 8 * self.lanes, "a level-0 leaf is the occupied lanes' K words");
        assert_eq!(l[0].log_msg_cols as usize + l[0].fold, self.stack_log);
        for i in 1..l.len() {
            assert_eq!(l[i].leaf_bytes, 16 << l[i].fold, "a level-{i} leaf is 2^fold E values");
            assert_eq!(l[i].log_msg_cols as usize + l[i].fold, l[i - 1].log_msg_cols as usize);
        }
        for x in l {
            assert_eq!(x.ht, x.log_msg_cols + x.log_inv_rate);
            assert!(x.lv <= x.ht);
        }
        let last = l.last().unwrap();
        assert_eq!(self.final_coeffs, (1 << last.log_msg_cols) + last.fold);
        assert_eq!(self.tail_rounds, last.log_msg_cols as usize);
    }
}

/// The season shape, from `fs6::params::P18`.
pub fn p18() -> Shape {
    of(fs6::params::P18, "P18")
}

/// R9: the shape at `n = 2^17` (FORMAT6 v2.6), from `fs6::params::P17`.
pub fn p17() -> Shape {
    of(fs6::params::P17, "P17")
}

/// R9: the shape this build verifies (`fs6::params::SHAPE`: the layout, `C_rec`'s window and the sponge's rows are
/// compiled for it, so `V_S` runs only there; see `refv/p17`).
pub fn active() -> Shape {
    if fs6::params::SHAPE.log_blocks == 17 { p17() } else { p18() }
}

fn of(p: fs6::params::Shape, name: &'static str) -> Shape {
    let s = Shape {
        name,
        log_blocks: p.log_blocks,
        stack_log: p.stack_log as usize,
        lanes: p.lanes,
        phi_vars: p.phi_vars,
        levels: p.levels.to_vec(),
        grind_batch: p.grind_batch,
        final_coeffs: p.final_coeffs,
        tail_rounds: p.tail_rounds,
        grind_tail: p.grind_tail,
        j0: p.j0,
        qv: p.qv,
    };
    s.check();
    s
}

/// The test shape `T15` (FORMAT6 v2.2 adopts it in place of `P8`): `M = 15`, folds 6, 3, 3, rate ¼, the
/// rate ladder of leanVM (`+fold−3` after level 0, `+fold−1` after), grinds of 8–10 bits (so that a byte tamper passes a PoW by chance with probability ≤ 2^-8) and small query counts. Leaves 368 B
/// and 128 B. Header and statement as `P18` (`n = 2^18`). Caps `2^3, 2^3, 2^2` (v2.2): with level 1's cap at `2^2`
/// the bind query after `CAP(1)` would be `32 + 96 + 128 = 256` bytes, which `fs6`'s transcript rejects (its
/// length list is `P18`'s; under `T15`'s own rule, leaves 368/128 and nodes 64, it would be allowed).
pub fn t15() -> Shape {
    let lvl = |ht, lv, leaf_bytes, queries, fold, log_msg_cols, log_inv_rate| Level {
        ht,
        lv,
        leaf_bytes,
        queries,
        fold,
        log_msg_cols,
        log_inv_rate,
        agreement_end: 0,
        grind_fold: 8,
        grind_ood: 9,
        grind_query: 10,
    };
    let s = Shape {
        name: "T15",
        log_blocks: 18,
        stack_log: 15,
        lanes: 46,
        phi_vars: fs6::params::PHI_VARS_PROVISIONAL,
        levels: vec![lvl(11, 3, 368, 13, 6, 9, 2), lvl(11, 3, 128, 7, 3, 6, 5), lvl(10, 2, 128, 14, 3, 3, 7)],
        grind_batch: 9,
        final_coeffs: 11,
        tail_rounds: 3,
        grind_tail: 8,
        j0: 1024,
        qv: 16384,
    };
    s.check();
    s
}

pub fn by_name(name: &str) -> Option<Shape> {
    match name.to_ascii_lowercase().as_str() {
        "p18" => Some(p18()),
        "p17" => Some(p17()),
        "t15" => Some(t15()),
        _ => None,
    }
}
