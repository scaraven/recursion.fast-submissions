-- New for lvm6 (WP SPH): the sponge phase of `prog6` (FORMAT6 v2.5.3 §6.3): K1's caller and core
-- `spCaller6 13`, then season 1's link `ksLinkProgE2 13 10 contRows6`, the output placed on the stack
-- as WP S's `TreeOut` (the sponge slices and claims 16–45 of §6.5).
import Lvm6KProgS6
import LvmE2VProgKS

/-!
# The sponge phase `spongePhase6`

FORMAT6 v2.5.3 §6.3 (caller C1–C2, core, link L1–L3) and §6.5 (claim order and placements). Light
(programs only), so that `Lvm6AsmProg.phases6` can use it.

* **`contRows6`**: the continuation rows of check L3, `[1, B) ∪ [K₁+1, K₁+32) ∪ [K₂+1, K₂+32)` at
  `B = 4,002` (WP CB's `blocks_P18`), `K₁ = 7,567`, `K₂ = 8,032`: WP CB's `rowsBK2 4002 7567 8032`
  written out.
* **`spS o lk`**: the caller's output `o = (r, v, (hd, en))` and the link's `lk = (kchal, kshift,
  vals)` as `TreeOut`. Placements (§6.5, §T, CD): the sponge block `SP` is slot 35 (word
  `x + 2^13·ℓ` at stack word `x + 2^13·ℓ + 2^19·35`), `Y` lane `ℓ` of row `x` at `x + 2^13·(36·64 + ℓ)`,
  the stream `M(x, ℓ)` at `17x + ℓ + 2^19·33`, `X(i, ℓ)` at `i + 2^10·(37·2^9 + ℓ)` (slot 37, words
  `ℓ·2^10 + i`). A block claim at `μ` variables becomes a 25-variable point claim whose high
  coordinates are the block index's bits (`bitsF`), as WP K1's tree claims (`K.toS`).
  - slices: the 64 slices at `(pt, bits 35)`;
  - claims, in order: 16 `c_out` at `(r, ϱm, bits 35)`; 17 + ℓ (`ℓ < 25`) the tied lanes `Ỹ_ℓ(r) = v_ℓ`;
    42 `Σ_ℓ eq(λ, ℓ)·Ỹ_ℓ(ρ')`; 43 `Σ_ℓ eq(λ, ℓ)·sp̃(ρ', slot ℓ)`; 44 `Σ_{ℓ<17} eq(λ, ℓ)·Σ_{x<7168}
    eq(ρ', x)·M(x, ℓ)` (cube weights at the stream words); 45 `Σ_{ℓ<17} eq(λ, ℓ)·X̃_ℓ(ρ'_{<10})`.
  Every weight is a combination of `eqPt p` with `|p| = 25` (multiaffine).
* **`spongePhase6 sh x`**: on shapes with `M = 25` and `P18`'s sponge items (`SpShapeOK`), the caller,
  the link, `spS`; rejection elsewhere.
-/

set_option autoImplicit false

namespace Lvm6.SP

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Lvm.E2V Finset

/-- **The continuation rows of check L3** (FORMAT6 §6.3 row map, `B = 4,002`). -/
def contRows6 : List ℕ :=
  ((List.range (4002 - 1)).map (· + 1) ++ (List.range 31).map (7567 + 1 + ·)) ++
    (List.range 31).map (8032 + 1 + ·)

/-- What the link returns: `kchal = ρ ++ λ`, `(ρ', final)`, `vals = (Y, in, M, X)`. -/
abbrev LinkOut : Type := List E2 × (List E2 × E2) × List E2

/-- Claim 16: `sp̃(r, ϱm) = c_out` on `SP` (slot 35). -/
def cOut (o : K.SpOut) : StackClaim6 :=
  (fun pt ↦ eqPt (o.1 ++ o.2.2.1.ϱm ++ bitsF 35 6) pt, o.2.2.1.cout)

/-- Claim `17 + ℓ`: `Ỹ_ℓ(r) = v_ℓ` (slot 36, block `36·64 + ℓ` of `2^13` words). -/
def cTied (o : K.SpOut) (l : ℕ) : StackClaim6 :=
  (fun pt ↦ eqPt (o.1 ++ bitsF (36 * 64 + l) 12) pt, o.2.1.getD l 0)

/-- Claim 42: `Σ_{ℓ<25} eq(λ, ℓ)·Ỹ_ℓ(ρ') = Y`. -/
def cY (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ l ∈ range 25, eqAtF (lk.1.drop 13) l * eqPt (lk.2.1.1 ++ bitsF (36 * 64 + l) 12) pt,
    lk.2.2.getD 0 0)

/-- Claim 43: `Σ_{ℓ<25} eq(λ, ℓ)·sp̃(ρ', slot ℓ) = in` (block `35·64 + ℓ`). -/
def cIn (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ l ∈ range 25, eqAtF (lk.1.drop 13) l * eqPt (lk.2.1.1 ++ bitsF (35 * 64 + l) 12) pt,
    lk.2.2.getD 1 0)

/-- Claim 44: `Σ_{ℓ<17} eq(λ, ℓ)·Σ_{x<7168} eq(ρ', x)·M(x, ℓ) = M`, `M(x, ℓ)` the stream word
`17x + ℓ` (slot 33). -/
def cM (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ i ∈ range 17 ×ˢ range 7168, eqAtF (lk.1.drop 13) i.1 * eqAtF lk.2.1.1 i.2 *
      eqPt (bitsF (17 * i.2 + i.1 + 2 ^ 19 * 33) 25) pt,
    lk.2.2.getD 2 0)

/-- Claim 45: `Σ_{ℓ<17} eq(λ, ℓ)·X̃_ℓ(ρ'_{<10}) = X` (slot 37, block `37·2^9 + ℓ` of `2^10` words). -/
def cX (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ l ∈ range 17, eqAtF (lk.1.drop 13) l *
      eqPt (lk.2.1.1.take 10 ++ bitsF (37 * 2 ^ 9 + l) 15) pt,
    lk.2.2.getD 3 0)

/-- **The sponge batch's output as WP S's `TreeOut`** (FORMAT6 §6.5 order, claims 16–45). -/
def spS (o : K.SpOut) (lk : LinkOut) : TreeOut :=
  ⟨⟨o.2.2.2.pt ++ bitsF 35 6, fun z ↦ o.2.2.2.s.getD z 0⟩,
    cOut o :: ((List.range 25).map (cTied o) ++ [cY lk, cIn lk, cM lk, cX lk])⟩

/-- The shapes the sponge phase serves: a stack of `2^25` words and `P18`'s sponge items. -/
def SpShapeOK (sh : Shape) : Prop := sh.M = 25 ∧ sh.spongePart = P18.spongePart

instance (sh : Shape) : Decidable (SpShapeOK sh) := by
  unfold SpShapeOK; infer_instance

/-- The caller and core (`2^13` rows, 25 tied lanes), the link (`xl = 10`), the placement. -/
def spongeBody : VerifierProgram TreeOut :=
  K.spCaller6 13 >>= fun o ↦ ksLinkProgE2 13 10 contRows6 >>= fun lk ↦ pure (spS o lk)

/-- **The sponge phase of `prog6`** (FORMAT6 §6.3). -/
def spongePhase6 (sh : Shape) (_x : Hdr) : VerifierProgram TreeOut :=
  if SpShapeOK sh then spongeBody else VerifierProgram.fail

end Lvm6.SP
