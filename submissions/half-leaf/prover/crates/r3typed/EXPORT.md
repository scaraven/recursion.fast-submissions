# What CD's generator exports (for R3; consumed by `r3typed::Circuit::from_blob` and an r3mb loader)

One text file, `q6.blob`. Tokens are ASCII and separated by whitespace (newlines only for readability). Integers are
decimal. An `E` value is `c0 c1`: the two `K` limbs as decimal `u64`, bit `z` being the coefficient of `x^z`
(FORMAT6 §1). Index conventions are FORMAT6's: stack index `r + 2^19·slot`; `C_rec` word `w` is stack index
`w + 2^19·33`.

```
Q6 1
TYPED n      then n lines:  src base log off
ENTS n       then n lines:  o x y c0 c1
OUT n        then n lines:  x y
CONST n      then n lines:  lo len v_0 … v_{len−1}
POWBITS n    then n lines:  w bw nb             (optional; PoW bit words, see below)
MINIBUS ns nr                                   (optional, r3mb's)
  ns lines:  limbs base stride tau v_0 … v_{limbs−1} fin
  nr lines:  limbs tau addr v_0 … v_{limbs−1} cnt
END
CHECKSUM <64 hex>                               (optional; Keccak-256 of every byte before "CHECKSUM")
```

## Q (the typed instance `TInst6`; Lean `Lvm6.Ty`)
- `TYPED`: the word space's regions (season 1's `TReg`). Words `base … base + 2^log − 1` map to targets
  `off …`. Both `base` and `off` must be multiples of `2^log`, and regions must not overlap. Each `src` is one of:
  - `com`: the typed result memory `T`; `off` is a stack index inside slots 37–45. A `com` region may cover `X`'s
    words; the witness then writes `X` (see the open item below).
  - `ks`: the `KS` aliases; `off` is a stack index (sponge outputs `Y`, slot 36).
  - `sflat`: one region of `2^19` words, `off = 0`.
  - `sigma`: one region of `2^11` words, `off = sB = 2^18` (CD §0).
  - `pub`: one region of `2^10` words. Word `base + i` is `HDR` lane `i` (`HDR` bytes `8i … 8i+7` LE; 103 lanes,
    zero after that).
  - `one`: every word of the region is 1.
  - `qlt`: values from `CONST`. CD has none; keep `CONST 0`.
  - A word in no region is 0.
- `ENTS`: the four matrices `M_o[x][y] += c` for `o ∈ {0: A, 1: B, 2: D, 3: W}`, with `x < 2^20`, `y < 2^21`,
  `c ∈ E`. The relation at every slot is `(M_0 z)(x)·(M_1 z)(x) + (M_2 z)(x) + (M_3 z)(x) = 0` in `E` (`relE`;
  `entsE`, the coordinate-0 entries). Order and duplicates are free: the loader sorts and merges. Bound:
  `PhiBudget`, ≤ 280,000 entries.
- `OUT`: the witness program, as a solve order. Row `x` defines `com` word `y`:
  `z_y = (A·B + C')·c_y^{-1}`, where `c_y` is the sum of `y`'s coefficients in `D` and `W` of row `x`, `C'` is the
  rest of `D z + W z`, and `y` occurs in neither `A` nor `B` of that row. The result must lie in `K`. Rows are
  solved in file order, after the `ks`, `sflat`, `sigma`, `pub` and `one` words have been read from the stack and
  header. A `com` word that no row defines is 0. If CD's witness is a program run instead (season 1's LoopIR), it
  ships as a separate file plus a dump of the `com` words; then `OUT` lists only rows that check.
- `Φ_Q(pt) = Σ_e c_e·eq(pt, o_e + 4·(x_e + 2^20·y_e))` in 43 variables: selector (2), then `x` (20), then `y` (21),
  low bit first (`PhiQE`). It is derived from `ENTS` alone, so it is not exported separately.
  `Φ_Q(0^43)` is the coefficient of entry `(o, x, y) = (0, 0, 0)`, or 0 if there is none. The leaf header's
  `accIn = (0^43, Φ_Q(0^43))` (FORMAT6 §2.1). For a cross-check, CD may add
  `# phi0 c0 c1` as a comment line *before* `Q6`. The loader ignores it; R3 compares it with `r3typed::phi_q`.

## PoW bit words (`POWBITS`, LAY)
Word `bw + i` (a `com` word, not in `OUT`) is bit `i` of `STREAM` word `w` (= `C_rec` word `w`: the child's PoW
lane), `i < nb = 64 − g`. They are a function of the child's trace (zero at `b = 0`), written by the witness before
the rows are solved. The section may be in the blob (before `END`, after `MINIBUS` if both) or in a sidecar file
`POWBITS n … END`: `$LVM6_Q_POW`, else `<blob stem>.pow` next to `$LVM6_Q_BLOB` (`r3typed::circuit::parse_powbits`).

## Mini-bus tables (`MINIBUS`; r3mb's `MbTab`: WP-9's memory checking, `mbLinB6` form)
Every column is a committed stack index (`MbCol::Com { at }`). The column covers `2^tau` words from `at`, and
`at` is `2^tau`-aligned. `limbs` is 1 for `K` cells (separator `g^3`) or 2 for `E` cells (separator `g^4`).
- **Seed** `limbs base stride tau v… fin`: the cells `base + stride·x` for `x < 2^tau`.
  - Address: a fixed column, `g^{base + stride·x}` (r3mb `seed_addr`).
  - Value limb `l`: column `v_l`. These words are written by the typed witness (`T`) or are `C_rec` words.
  - Finalize column: `fin`, written by r3mb (`g^{reads}`).
- **Read** `limbs tau addr v… cnt`: one read per row.
  - Address column: `addr` (the read cell's `g^{cell}`).
  - Value limbs: columns `v_l`.
  - Count column: `cnt`, written by r3mb (`g^k` for the cell's `k`-th read).
- r3mb places only the columns it writes (`fin`, `cnt`). They go in `MB_LO … MB_HI` (slot 36, words ≥ 2^18). The
  address and value columns are words of `T`, or of `C_rec` for seeds of stream cells (season 1: stride 17, now
  stride 1).
- Ordering: seeds first, then reads, as in season 1's `MINIBUS` section (`typed_blob.rs`).
- Loader: `r3typed::circuit::parse_minibus(text) -> Option<MbExport>` returns these rows; r3mb builds its
  `MbSpec`/`MbTab` from them, reading the value columns from the stack after the typed witness has run.

## `X` (the sponge link's message cells, FORMAT6 §6.3 L3, claim 45)
- Placement: `X(i, l)` is the message lane `l < 17` of sponge row `split + i`, with `i < 2^10` and
  `split = 2^13 − 2^10`. It sits at stack index `x_idx(i, l) = ((X_OFF0 + l) << 10) + i`, i.e. slot 37 words
  `l·2^10 + i` (`r3core::layout`, STUB until CD confirms).
- Cell sources: the message lanes the circuit absorbs in its own sponge rows (the `σ_leaf` WOTS walk and the
  child-trace sponge). CD exports them as `com` regions of `log 10` with `off = x_idx(0, l)`, one per lane, and
  defines their words through `OUT` like any other `T` word.
- Open item (ordering): `X` feeds the sponge witness (`Y`), and `Y` feeds the typed rows through `ks`. CD must
  either (a) order `OUT` so that the `X` words do not depend on `ks` words of rows `≥ split`, letting the driver run
  typed (`X` part) → sponge → typed (rest); or (b) export `X`'s values directly as a `CONST`-like dump.
