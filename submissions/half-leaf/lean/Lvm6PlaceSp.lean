-- New for lvm6 (PORT17, package L2; P17-freeze §5 "not in any package": the sponge phase's placement). The sponge
-- phase's claims (`Lvm6SpProg`) read from the placement record (`Lvm6Place`); each equals the deployed definition
-- (`P17`) at `place17`, and `place18` gives the INT10 claims.
import Lvm6Place
import Lvm6SpProg

/-!
# The sponge phase's placement over `Place` (PORT17 L2)

`Lvm6SpProg` fixes (at `P17`) `SP` at slots 34–35 (`bitsF 17 5`), `Y` at `40·32 + ℓ` (11 bits), `SP`'s lanes at
`17·64 + ℓ`, the stream at `2^18·33` (24 bits) and `X` at `42·2^8 + ℓ` (14 bits). Here they are the record's:

* `SP`: selector `spSel` on `spSelBits` bits (`place17`: 17 on 5 bits, P17-freeze finding 4);
* `Y`, `SP`'s lanes: lane indices `yIdx + ℓ`, `spIdx + ℓ` on `M − yLog` bits (`place17`: `40·32`, `17·64`, 11 bits);
* the stream word `17x + ℓ` at `recOff` on `M` bits (`place17`: `33·2^18`, 24 bits);
* `X`: the first `xLog` coordinates of `ρ'`, lane index `xIdx + ℓ` on `M − xLog` bits (`place17`, fallback:
  `42·2^8`, 14 bits);
* the link's continuation rows at `B`, `K₁`, `K₂` (`place17`: `B = 3,816`).

`spongePhase6` itself is not restated: it reads `SpShapeOK sh` (`sh.M = 24 ∧ sh.spongePart = P18.spongePart`,
`P17`). Its generic form is `if SpShapeOK sh then spongeBodyP pl else fail` with the pin `sh.M = pl.M` (and
`pl.Fits sh`); `Lvm6SpPhase`'s proofs (`block25`, `claims_of_holds` at `bitsF 35 6`) are V1's.
-/

set_option autoImplicit false

namespace Lvm6.SP

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Lvm.E2V Finset

variable (pl : Place)

/-- **The continuation rows of check L3**: `[1, B) ∪ [K₁+1, K₁+32) ∪ [K₂+1, K₂+32)`. -/
def contRowsP : List ℕ :=
  ((List.range (pl.B - 1)).map (· + 1) ++ (List.range 31).map (pl.K₁ + 1 + ·)) ++
    (List.range 31).map (pl.K₂ + 1 + ·)

/-- Claim 16: `sp̃(r, ϱm) = c_out` on `SP` (selector `spSel` on `spSelBits` bits). -/
def cOutP (o : K.SpOut) : StackClaim6 :=
  (fun pt ↦ eqPt (o.1 ++ o.2.2.1.ϱm ++ bitsF pl.spSel pl.spSelBits) pt, o.2.2.1.cout)

/-- Claim `17 + ℓ`: `Ỹ_ℓ(r) = v_ℓ` (lane `yIdx + ℓ` of `2^yLog` words). -/
def cTiedP (o : K.SpOut) (l : ℕ) : StackClaim6 :=
  (fun pt ↦ eqPt (o.1 ++ bitsF (pl.yIdx + l) (pl.M - pl.yLog)) pt, o.2.1.getD l 0)

/-- Claim 42: `Σ_{ℓ<25} eq(λ, ℓ)·Ỹ_ℓ(ρ') = Y`. -/
def cYP (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ l ∈ range 25, eqAtF (lk.1.drop 13) l * eqPt (lk.2.1.1 ++ bitsF (pl.yIdx + l) (pl.M - pl.yLog)) pt,
    lk.2.2.getD 0 0)

/-- Claim 43: `Σ_{ℓ<25} eq(λ, ℓ)·sp̃(ρ', lane ℓ) = in` (lane `spIdx + ℓ`). -/
def cInP (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ l ∈ range 25, eqAtF (lk.1.drop 13) l * eqPt (lk.2.1.1 ++ bitsF (pl.spIdx + l) (pl.M - pl.yLog)) pt,
    lk.2.2.getD 1 0)

/-- Claim 44: `Σ_{ℓ<17} eq(λ, ℓ)·Σ_{x<7168} eq(ρ', x)·M(x, ℓ) = M`, `M(x, ℓ)` the stream word `17x + ℓ`. -/
def cMP (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ i ∈ range 17 ×ˢ range pl.split, eqAtF (lk.1.drop 13) i.1 * eqAtF lk.2.1.1 i.2 *
      eqPt (bitsF (17 * i.2 + i.1 + pl.recOff) pl.M) pt,
    lk.2.2.getD 2 0)

/-- Claim 45: `Σ_{ℓ<17} eq(λ, ℓ)·X̃_ℓ(ρ'_{<xLog}) = X` (lane `xIdx + ℓ` of `2^xLog` words). -/
def cXP (lk : LinkOut) : StackClaim6 :=
  (fun pt ↦ ∑ l ∈ range 17, eqAtF (lk.1.drop 13) l *
      eqPt (lk.2.1.1.take pl.xLog ++ bitsF (pl.xIdx + l) (pl.M - pl.xLog)) pt,
    lk.2.2.getD 3 0)

/-- **The sponge batch's output as `TreeOut`** (claims 16–45). -/
def spSP (o : K.SpOut) (lk : LinkOut) : TreeOut :=
  ⟨⟨o.2.2.2.pt ++ bitsF pl.spSel pl.spSelBits, fun z ↦ o.2.2.2.s.getD z 0⟩,
    cOutP pl o :: ((List.range 25).map (cTiedP pl o) ++ [cYP pl lk, cInP pl lk, cMP pl lk, cXP pl lk])⟩

/-- The caller and core (`2^yLog` rows), the link (`xl = xLog`), the placement. -/
def spongeBodyP : VerifierProgram TreeOut :=
  K.spCaller6 pl.yLog >>= fun o ↦ ksLinkProgE2 pl.yLog pl.xLog (contRowsP pl) >>= fun lk ↦ pure (spSP pl o lk)

/-! ## `place18` is today's sponge phase -/

theorem contRows6_eq : contRows6 = contRowsP place17 := rfl
theorem cOut_eq : cOut = cOutP place17 := rfl
theorem cTied_eq : cTied = cTiedP place17 := rfl
theorem cY_eq : cY = cYP place17 := rfl
theorem cIn_eq : cIn = cInP place17 := rfl
theorem cM_eq : cM = cMP place17 := rfl
theorem cX_eq : cX = cXP place17 := rfl
theorem spS_eq : spS = spSP place17 := rfl
theorem spongeBody_eq : spongeBody = spongeBodyP place17 := rfl

/-- **The `P17` constants** the sponge claims read (P17-freeze §2.2 §6.5, §3.3 with `X` at slot 42). -/
theorem place17_sp : place17.spSel = 17 ∧ place17.spSelBits = 5 ∧ place17.yIdx = 40 * 32 ∧
    place17.spIdx = 17 * 64 ∧ place17.M - place17.yLog = 11 ∧ place17.recOff = 2 ^ 18 * 33 ∧ place17.M = 24 ∧
    place17.xLog = 10 ∧ place17.xIdx = 42 * 2 ^ 8 ∧ place17.M - place17.xLog = 14 ∧ place17.yLog = 13 ∧
    contRowsP place17 = ((List.range (3816 - 1)).map (· + 1) ++ (List.range 31).map (7567 + 1 + ·)) ++
      (List.range 31).map (8032 + 1 + ·) := by
  refine ⟨by decide, rfl, by decide, by decide, rfl, by decide, rfl, rfl, by decide, rfl, rfl, rfl⟩

/-- **The sponge phase serves `P17`** (`spongePhase6 P17` runs the body). -/
theorem spShapeOK_P17 : SpShapeOK P17 := by decide +kernel

end Lvm6.SP
