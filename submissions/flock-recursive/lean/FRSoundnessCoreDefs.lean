-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-1): the position-free
-- declarations of the 3.x soundness modules that revision 4.1 reuses, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessDefs` (12). Content: the potential's generic parts
-- that do not read the item list (`L₀`, `EscAtG`, `StabExt`, `lastAns`, `ext1`, `ext`, `condCount`,
-- `pRoundG`, `badCount_frac_le`). The 3.x modules import this one.
import FRLog

/-! ## From `FRSoundnessDefs` (12 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle

open scoped NNReal

/-- The log strictly before entry `j` (the prefix a chain ending at `j` is charged on). -/
def L₀ (L : Log) (j : ℕ) : Log := L.take j

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

/-- **`EscAt`**: the chain `es` (of at least two entries) was doomed before its last entry and is
not after it, both on the log `L₀`. -/
def EscAtG (L₀ es : Log) : Prop := 2 ≤ es.length ∧ D L₀ es.dropLast ∧ ¬ D L₀ es

variable {D φ}

/-- **The H row** (§5.2): the bad fraction of a fresh answer is at most `2^-142`. -/
theorem badCount_frac_le : (badCount : ℝ≥0) / 2 ^ 256 ≤ (2 : ℝ≥0)⁻¹ ^ 142 := by
  rw [div_le_iff₀ (by positivity), inv_pow, ← div_eq_inv_mul,
    le_div_iff₀ (by positivity), badCount]
  norm_num

end Potential

section Ext

/-- The answer of the last entry (`default` for the empty list). -/
def lastAns (es : Log) : Digest := (es.getLast?.map Prod.snd).getD default

/-- The chain extended by the squeeze of its last answer, answered `a`. -/
def ext1 (es : Log) (a : Digest) : Log := es ++ [(squeezeQ (lastAns es), a)]

/-- The formal extension of `es` by the answers `as`, each a squeeze of the previous answer. -/
def ext (es : Log) (as : List Digest) : Log := as.foldl ext1 es

variable (D : Log → Log → Prop)

open Classical in
/-- **`condCount`**: the conditional count of the escape `EscAt (ext es₀ ·)` of a phase of `r`
answers entered at `es₀`, given its first answers `pre`, as a fraction of `2^256` per missing
answer. -/
noncomputable def condCount (L₀ es₀ : Log) (r : ℕ) (pre : List Digest) : ℝ≥0 :=
  (extCount (fun as => EscAtG D L₀ (ext es₀ as)) pre (r - pre.length) : ℝ≥0) /
    2 ^ (256 * (r - pre.length))

end Ext

section Local

theorem ext_nil (es : Log) : ext es [] = es := rfl

theorem ext_append (es : Log) (as : List Digest) (a : Digest) :
    ext es (as ++ [a]) = ext1 (ext es as) a := by
  simp [ext, List.foldl_append]

theorem ext_dropLast (es₀ : Log) {as : List Digest} (h : as ≠ []) :
    (ext es₀ as).dropLast = ext es₀ as.dropLast := by
  conv_lhs => rw [← List.dropLast_append_getLast h, ext_append]
  rw [ext1, List.dropLast_concat]

/-- **The extensions on which `hloc_of` reads the doom off the charging log**: inside a
multi-squeeze phase `(s0, r)` entered strictly before the chain's last entry, the chain's first
`s0 + 1` entries extended formally by at most `r` answers. With `RndOK rnd` the formal entries sit
on the phase's squeeze positions, so every absorb entry of such an extension (every cap) is a real
chain entry before the last. -/
def StabExt (rnd : ℕ → Option (ℕ × ℕ)) (es X : Log) : Prop :=
  ∃ s0 r as, rnd (s0 + 1) = some (s0, r) ∧ s0 + 1 < es.length ∧ as.length ≤ r ∧
    X = ext (es.take (s0 + 1)) as

variable (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ))

/-- **The charge**: inside a multi-squeeze phase, after `1 ≤ k < r` answers, the conditional count
of its escape (on the log `L`); `0` elsewhere. -/
noncomputable def pRoundG (L es : Log) : ℝ≥0 :=
  match rnd (es.length - 1) with
  | some (s0, r) =>
    if es.length - 1 - s0 < r then
      condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd)
    else 0
  | none => 0

variable {D rnd}

end Local

end FR.Snd
