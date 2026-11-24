//! `docs/lvm6/wp/PARAM/params6.json` (frozen 2026-11-22) and FORMAT6's `Shape` as constants: the prover reads
//! every WHIR parameter from here, never from leanVM's `f64` search (FORMAT6 §9, P1 §5). `tests::matches_json`
//! checks these literals against the JSON file when it is present.

/// One WHIR level (FORMAT6 §5 table, `params6.json` `levels[i]`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Level {
    /// `log2` of the positions (= leaves): `log_msg_cols + log_inv_rate`.
    pub ht: u32,
    /// `log2` of the cap.
    pub lv: u32,
    /// Bytes of one leaf: 368 at level 0 (46 `K` words), 256 at levels 1–4 (16 `E` values).
    pub leaf_bytes: usize,
    /// Openings `t`.
    pub queries: usize,
    /// Fold rounds `ℓ` (initial fold at level 0).
    pub fold: usize,
    pub log_msg_cols: u32,
    pub log_inv_rate: u32,
    pub agreement_end: u64,
    pub grind_fold: u32,
    pub grind_ood: u32,
    pub grind_query: u32,
}

impl Level {
    /// Path queries of one opening: `ht − lv` node queries.
    pub const fn path(&self) -> usize {
        (self.ht - self.lv) as usize
    }
    /// Positions one draw gives: `⌊128/ht⌋`.
    pub const fn per_draw(&self) -> usize {
        128 / self.ht as usize
    }
    /// Draws for the positions: `⌈t / ⌊128/ht⌋⌉`.
    pub const fn position_draws(&self) -> usize {
        self.queries.div_ceil(self.per_draw())
    }
    /// Bytes of one opening in `BODY`: the leaf and `ht − lv` siblings.
    pub const fn opening_bytes(&self) -> usize {
        self.leaf_bytes + 32 * self.path()
    }
    /// Cap bytes `32·2^lv`.
    pub const fn cap_bytes(&self) -> usize {
        32 << self.lv
    }
}

/// FORMAT6's `Shape` (the constants V_S, R1 and the prover share). Sub-schedules of §T are not frozen: their
/// counts are not here (see `schedule.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// `log2 N★` (blocks of a leaf): 18.
    pub log_blocks: u32,
    /// Stack variables `M`: 25.
    pub stack_log: u32,
    /// Tree batch `κ` and sponge batch `κ_s`.
    pub kappa: u32,
    pub kappa_s: u32,
    /// Occupied stack lanes (slots): 46.
    pub lanes: usize,
    /// `v = phiVars` of the accumulator point in `HDR` (≤ 56). NOT FROZEN (§T, CD): provisional value.
    pub phi_vars: usize,
    /// The WHIR levels (FORMAT6 v2.2: generic in their number; `P18` has 5, refv's `T15` 3).
    pub levels: &'static [Level],
    /// `λ₀` batch grind (§6.5).
    pub grind_batch: u32,
    /// Final polynomial coefficients sent at level 4 (`2^3 + 4`).
    pub final_coeffs: usize,
    /// Tail sumcheck rounds after `OPEN(4)` and their grind.
    pub tail_rounds: usize,
    pub grind_tail: u32,
    /// `J₀`: `V_S` rejects more stacked claims.
    pub j0: usize,
    /// `qV` of `claim.json`.
    pub qv: usize,
}

const fn level(
    ht: u32,
    lv: u32,
    leaf_bytes: usize,
    queries: usize,
    fold: usize,
    log_msg_cols: u32,
    log_inv_rate: u32,
    agreement_end: u64,
    grind_query: u32,
) -> Level {
    Level { ht, lv, leaf_bytes, queries, fold, log_msg_cols, log_inv_rate, agreement_end, grind_fold: 10, grind_ood: 18, grind_query }
}

const P18_LEVELS: [Level; 5] = [
    level(21, 7, 368, 110, 6, 19, 2, 1_053_300, 19),
    level(20, 6, 256, 45, 4, 15, 5, 188_173, 17),
    level(19, 5, 256, 28, 4, 11, 8, 34_227, 18),
    level(18, 5, 256, 21, 4, 7, 11, 6_525, 17),
    level(17, 5, 256, 18, 4, 3, 14, 1_548, 13),
];

/// `P18`, the season shape (rate ¼, `M = 25`).
pub const P18: Shape = Shape {
    log_blocks: 18,
    stack_log: 25,
    kappa: 19,
    kappa_s: 13,
    lanes: 46,
    phi_vars: PHI_VARS_PROVISIONAL,
    levels: &P18_LEVELS,
    grind_batch: 17,
    final_coeffs: 12,
    tail_rounds: 3,
    grind_tail: 2,
    j0: 1024,
    qv: 16384,
};

/// `phiVars` (FORMAT6 v2.3: `κ ∈ E^2`, `r_x ∈ E^20`, `r_y ∈ E^21`, so 43; `|HDR| = 824`). PARAM's bound is 56.
/// The name is kept from v2.2, when the value was provisional.
pub const PHI_VARS_PROVISIONAL: usize = 2 + TY_X + TY_Y;

/// §6.4a's zerocheck variables (`r_x`) and wiring variables (`r_y`).
pub const TY_X: usize = 20;
pub const TY_Y: usize = 21;
/// §6.4a's relayout rounds.
pub const TY_RELAYOUT: usize = 19;
/// §6.4b's mini-bus steps (depth).
pub const MB_STEPS: usize = 6;

/// The WHIR prover configuration of a shape, in leanVM's `ProverConfig` terms: per-level `log_inv_rate`, the
/// initial fold, the later folds, the per-level query counts.
pub struct WhirFrozen {
    pub log_inv_rates: Vec<usize>,
    pub initial_k: usize,
    pub level_ks: Vec<usize>,
    pub queries: Vec<usize>,
}

impl Shape {
    pub fn whir(&self) -> WhirFrozen {
        let l = self.levels;
        WhirFrozen {
            log_inv_rates: l.iter().map(|x| x.log_inv_rate as usize).collect(),
            initial_k: l[0].fold,
            level_ks: l[1..].iter().map(|x| x.fold).collect(),
            queries: l.iter().map(|x| x.queries).collect(),
        }
    }

    /// The lengths no chain query of this shape may have: the node class (64) and every level's leaf (§3).
    pub fn forbidden_lengths(&self) -> Vec<usize> {
        let mut v = vec![64];
        for l in self.levels {
            if !v.contains(&l.leaf_bytes) {
                v.push(l.leaf_bytes);
            }
        }
        v
    }

    /// `|HDR| = 136 + 16v` (v2.2: `vk` is a header field).
    pub const fn hdr_len(&self) -> usize {
        136 + 16 * self.phi_vars
    }

    /// The level whose tree has `2^ht` leaves, if any (in `P18` the heights 21…17 are distinct).
    pub fn level_of_height(&self, ht: u32) -> Option<usize> {
        self.levels.iter().position(|l| l.ht == ht)
    }
}

/// PARAM's admission rule as a grind: the least `g ≥ 1` with `8c ≤ 7·2^g` for a group of error `c/|E|`
/// (`params6.json` `target.admit`; `⌈log₂(8c/7)⌉`, at least 1: every challenge follows a nonce, FORMAT6 §4).
/// Every group outside WHIR takes it (1 for `c = 1`; 2 for 2–3; 3 for 4–6; 5 for `ρ`'s 18; 6 for `s`'s 46). WHIR's
/// grinds are `Level`'s constants (fold 10, OOD 18, query per level, batch 17): admissible, chosen by PARAM's cost
/// search, not least.
pub const fn grind_for(c: u128) -> u32 {
    let mut g = 1;
    while g < 64 && 8 * c > 7 * (1u128 << g) {
        g += 1;
    }
    g
}

/// The frozen WHIR configuration for a stack of `2^log_n` words at L0 rate `2^-log_inv_rate`, if it is `P18`'s.
pub fn frozen_whir(log_n: usize, log_inv_rate: usize) -> Option<WhirFrozen> {
    (log_n == P18.stack_log as usize && log_inv_rate == P18.levels[0].log_inv_rate as usize).then(|| P18.whir())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `grind_for` on every group of `params6.json`: equal to the group's grind outside WHIR, admissible everywhere.
    #[test]
    fn grind_rule_matches_groups() {
        assert_eq!([1u128, 2, 3, 4, 6, 8, 18, 46, 45, 32768].map(grind_for), [1, 2, 2, 3, 3, 4, 5, 6, 6, 16]);
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../docs/lvm6/wp/PARAM/params6.json");
        let Ok(text) = std::fs::read_to_string(path) else { return };
        let j: String = text.chars().filter(|c| !c.is_whitespace()).collect();
        let mut n = 0;
        for chunk in j.split("{\"phase\":\"").skip(1) {
            let phase = &chunk[..chunk.find('"').unwrap()];
            let num = |k: &str| -> u128 {
                let at = chunk.find(k).unwrap() + k.len();
                chunk[at..].split(|c: char| !c.is_ascii_digit()).next().unwrap().parse().unwrap()
            };
            let (c, g) = (num("\"numerator_ceil\":"), num("\"grind\":") as u32);
            assert!(8 * c <= 7 * (1u128 << g), "{phase}: c {c} not admitted at g {g}");
            if phase != "whir" {
                assert_eq!(grind_for(c), g, "{phase}: c {c}");
            } else if !chunk.contains("fold") {
                assert!(grind_for(c) <= g);
            }
            n += 1;
        }
        assert_eq!(n, 51, "51 groups");
    }

    /// The literals against `params6.json` (skipped when the file is not beside the workspace).
    #[test]
    fn matches_json() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../docs/lvm6/wp/PARAM/params6.json");
        let Ok(text) = std::fs::read_to_string(path) else {
            eprintln!("params6.json not found at {path}: skipped");
            return;
        };
        let j: String = text.chars().filter(|c| !c.is_whitespace()).collect();
        let list = |xs: &[u64]| xs.iter().map(u64::to_string).collect::<Vec<_>>().join(",");
        let l = P18.levels;
        let has = |s: String| assert!(j.contains(&s), "params6.json lacks {s}");
        has(format!("\"stack_log_M\":{}", P18.stack_log));
        has(format!("\"log_inv_rate_0\":{}", l[0].log_inv_rate));
        has(format!("\"initial_fold\":{}", l[0].fold));
        has(format!("\"subsequent_fold\":{}", l[1].fold));
        has(format!("\"final_coefficients\":{}", P18.final_coeffs));
        has(format!("\"leaf0_lanes\":{}", P18.lanes));
        has(format!("\"stacked_claims_bound_J0\":{}", P18.j0));
        has(format!("\"grind_batch\":{}", P18.grind_batch));
        has(format!("\"qV\":{}", P18.qv));
        has(format!("\"queries\":[{}]", list(&l.iter().map(|x| x.queries as u64).collect::<Vec<_>>())));
        has(format!("\"log_caps\":[{}]", list(&l.iter().map(|x| x.lv as u64).collect::<Vec<_>>())));
        has(format!("\"fold\":[{}]", list(&l.iter().map(|x| x.grind_fold as u64).collect::<Vec<_>>())));
        has(format!("\"ood\":[{}]", list(&l.iter().map(|x| x.grind_ood as u64).collect::<Vec<_>>())));
        has(format!("\"query\":[{}]", list(&l.iter().map(|x| x.grind_query as u64).collect::<Vec<_>>())));
        has(format!("\"tail_round\":{}", P18.grind_tail));
        for x in l {
            has(format!(
                "\"log_msg_cols\":{},\"log_inv_rate\":{},\"fold\":{},\"log_block\":{},\"agreement_end\":{}",
                x.log_msg_cols, x.log_inv_rate, x.fold, x.ht, x.agreement_end
            ));
            has(format!("\"queries\":{},\"log_cap\":{},\"grind_fold\":{},\"grind_ood\":{},\"grind_query\":{}",
                x.queries, x.lv, x.grind_fold, x.grind_ood, x.grind_query));
            assert_eq!(x.ht, x.log_msg_cols + x.log_inv_rate);
        }
        // the ladder: each level's columns are the previous level's after its fold (stack 25 = 19 + 6)
        assert_eq!(l[0].log_msg_cols as usize + l[0].fold, P18.stack_log as usize);
        for i in 1..5 {
            assert_eq!(l[i].log_msg_cols as usize + l[i].fold, l[i - 1].log_msg_cols as usize);
        }
        // the final polynomial: 2^residual + 4 coefficients, residual = level 4's columns
        assert_eq!(P18.final_coeffs, (1 << l[4].log_msg_cols) + 4);
    }
}
