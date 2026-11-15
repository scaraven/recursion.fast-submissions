-- New for lvm2 E2F (slice S1, E2F-QH2): `C_main`'s opening at S2GF with the front's `E2` claims (V's
-- `LvmDecideE2.frontClaimsD`/`dOpenF`): the split halves of `E2` word/sum claims (weight a coordinate of `sumW6D`, in
-- `Quad Ext3`), the row-switch claims (weight `Σ_j ρ_j tensorW_j`, `LvmQRingCrt`), the pin first; both shapes. The
-- `E3` claim forms (`CClaim`, `LvmQAsmHarBase`) and their basis are reused unchanged (S2GM stays byte-identical).
import LvmE2QPin
import LvmQRingCrt
import LvmE2QW

/-!
# The opening at S2GF (`openGF`)

**Claims** (`FClaim`), in V's order (`dOpenF`): `e3 cc` (an `E3` claim: the typed and table claims, the boundary
claims), `half h parts v` (coordinate `h` of an `E2` sum claim on the whole stack, `splitD`: weight
`coord_h (Σ c·eqAbove_blk(x)·wordW(z, x))`, value the `K` cell `v`), `dhalf h z v` (a `D` word claim's half,
`parts = [(1, ⟨22, 0⟩, z)]`, tail `tailDE2`), `row blk z nu v` (a row claim on a regular block), `drow z nu v` (the
tape's row claim on `⟨ν, 0⟩`, tail `rowTailE2`).

**Word weight** (`w6Leaf`): `wordW(z, x) = Π_l ((1 + a_l + x_l) + b_l X)` in `E3[X]/(X² + xX + 1)` (`z_l = a_l + b_l X`;
`wordWD`'s factor `z_l x_l + (1 + z_l)(1 + x_l)`), memoised on `z`; the part's coefficient `c` multiplies last.

**Small shape** (`LvmQShapeF`: a small child's claims are big-form claims at `rotZ x`): regular halves and the `KS`
row claim are term pairs (big key, moved key, one leaf; `rgPair`'s form); a `D` half becomes the half with
coefficient `mux(s, 1, κ)` and point `z₀…₁₇ ‖ mux(s, z₁₈, z₂₀), mux(s, z₁₉, z₂₁), mux(s, z₂₀, 0), mux(s, z₂₁, 0)`
(`dClaimG`'s), value `v + s·tail_h`; the tape's row claim the same point and the extra factor `κ ⊗ 1`
(`onStackZB_ring`'s), value `v + s·rowTail`. `s` is the shape cell as a `K` cell (`sK`) and as an `E` cell.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape

/-! ## Claims -/

/-- A claim of `C_main`'s opening at S2GF. -/
inductive FClaim where
  /-- An `E3` claim. -/
  | e3 (cc : CClaim)
  /-- Coordinate `h` of an `E2` sum claim on the whole stack (parts: coefficient, block, point). -/
  | half (h : Bool) (parts : List (C2 × Placement × List C2)) (v : Cell)
  /-- Coordinate `h` of a `D` word claim (point `z`, 22 coordinates). -/
  | dhalf (h : Bool) (z : List C2) (v : Cell)
  /-- A row claim on a regular block. -/
  | row (blk : Placement) (z : List C2) (nu : RowNu) (v : Cell)
  /-- The tape's row claim on `⟨ν, 0⟩`. -/
  | drow (z : List C2) (nu : RowNu) (v : Cell)

/-- The cells the opening's gadgets share. -/
structure FCtx where
  /-- `E` zero and one. -/
  z : Cell
  o : Cell
  /-- `K` zero. -/
  zk : Cell
  /-- `E2` zero and one. -/
  z2 : C2
  o2 : C2

/-! ## The word weight -/

/-- The memo of word weights: point cells ↦ `(re, im)` of `wordW(z, X)`. -/
abbrev Memo6 := List (List C2 × Cell × Cell)

/-- The product of the factors `(1 + a_l + X_l) + b_l X` from coordinate `l` (`none`: no factor yet). -/
def wordGo (F : FCtx) (xb : Nat) : Nat → Option (Cell × Cell) → List C2 → BM (Option (Cell × Cell))
  | _, a, [] => pure a
  | l, a, c :: cs =>
    lin .E 1 1 (ec (xb + l)) c.re >>= fun α =>
    (match a with
      | none => pure (some (α, c.im))
      | some (A, B) => qmul FK.x F.z A B α c.im >>= fun r => pure (some r)) >>= fun a' =>
    wordGo F xb (l + 1) a' cs

/-- `wordW(z, X)` at the `E` cells `xb + l` (memoised). -/
def wordWG (F : FCtx) (xb : Nat) (zl : List C2) (m : Memo6) : BM (Memo6 × Cell × Cell) :=
  match m.find? (fun e => e.1 == zl) with
  | some e => pure (m, e.2)
  | none =>
    wordGo F xb 0 none zl >>= fun r =>
    let w := r.getD (F.o, F.z)
    pure ((zl, w) :: m, w)

/-- **A part's word leaf**: `coord (c · wordW(z, X))`, both coordinates. -/
def w6Leaf (F : FCtx) (xb : Nat) (c : C2) (zl : List C2) (m : Memo6) : BM (Memo6 × Cell × Cell) :=
  wordWG F xb zl m >>= fun r => qmul FK.x F.z r.2.1 r.2.2 c.re c.im >>= fun w => pure (r.1, w)

/-! ## Muxing (small shape) -/

/-- `mux(s, a, b) = a + s·(a + b)` on `E2` (`s` a `K` cell). -/
def mux2 (F : FCtx) (sK : Cell) (a b : C2) : BM C2 := g2Add a b >>= fun d => g2Mul (kC2 sK F.zk) d a

/-- `κ(z) = (1 + z₁₈)(1 + z₁₉)`. -/
def kappa2 (F : FCtx) (z : List C2) : BM C2 :=
  g2One (z.getD 18 default) >>= fun a => g2One (z.getD 19 default) >>= fun b => g2Mul a b F.z2

/-- The muxed `D`-region point and scale: `(mux(s, 1, κ), z₀…₁₇ ‖ m₁₈ m₁₉ m₂₀ m₂₁ ‖ z₂₂…)`. -/
def muxD (F : FCtx) (sK : Cell) (z : List C2) (κ : C2) : BM (C2 × List C2) :=
  mux2 F sK F.o2 κ >>= fun κm =>
  mux2 F sK (z.getD 18 default) (z.getD 20 default) >>= fun m18 =>
  mux2 F sK (z.getD 19 default) (z.getD 21 default) >>= fun m19 =>
  mux2 F sK (z.getD 20 default) F.z2 >>= fun m20 =>
  mux2 F sK (z.getD 21 default) F.z2 >>= fun m21 =>
  pure (κm, z.take 18 ++ [m18, m19, m20, m21] ++ z.drop 22)

/-- `zF(a, b) = Σ_l eq((a, b), l)·z*_l` on `E2` (`LvmQShapeC.zsumG`). -/
def zF2 (F : FCtx) (a b : C2) : BM C2 :=
  g2Mul a b F.z2 >>= fun ab =>
  g2Lin (zK 0 + zK 1) (FE2.ofK (zK 0)) F.z2 a >>= fun u1 =>
  g2Lin (zK 0 + zK 2) 0 u1 b >>= fun u2 =>
  g2Lin (zK 0 + zK 1 + zK 2 + zK 3) 0 u2 ab

/-- `L_ρ(u) = Σ_j ρ_j bit_j(u) = Σ_k ν0_k u_re^(2^k) + ν1_k u_im^(2^k)`. -/
def lRhoG (F : FCtx) (nu : RowNu) (u : C2) : BM Cell :=
  frobsK F.zk u.re >>= fun fr => frobsK F.zk u.im >>= fun fi =>
  (List.range 64).foldl (fun (m : BM Cell) k => m >>= fun acc =>
    mulAdd .E (nu.nu0.getD k default) (fr.getD k default) acc >>= fun a1 =>
    mulAdd .E (nu.nu1.getD k default) (fi.getD k default) a1) (pure F.z)

/-- **The tape row claim's tail** (`rowTailE2`): `Σ_l z*_l·L_ρ(u_l)`, `u_l = (1 + κ)·Π_{i≥22}(1 + z_i)·eq((z₂₀, z₂₁), l)`. -/
def rowTailG (F : FCtx) (nu : RowNu) (z : List C2) (κ : C2) : BM Cell :=
  g2One κ >>= fun mass =>
  g2Eq0 F.z2 mass (z.drop 22) >>= fun mb =>
  g2EqTab F.z2 [mb] [z.getD 20 default, z.getD 21 default] >>= fun us =>
  mapB (lRhoG F nu) us >>= fun Ls =>
  linSumE F.z ((List.range 4).map fun l => (zK l, Ls.getD l default))

/-! ## Prepared claims -/

/-- A claim prepared for the basis: its form and whether it is regular (moved in the small shape). -/
inductive PF where
  | e3 (cc : CClaim) (reg : Bool)
  | half (h : Bool) (parts : List (C2 × Placement × List C2)) (reg : Bool)
  | row (blk : Placement) (z : List C2) (κ : Option C2) (nu : RowNu) (reg : Bool)

/-- **The big-shape preparation** (no muxing). -/
def prepB (F : FCtx) : FClaim → PF × Cell
  | .e3 cc => (.e3 cc false, cc.value)
  | .half h parts v => (.half h parts false, v)
  | .dhalf h z v => (.half h [(F.o2, ⟨22, 0⟩, z)] false, v)
  | .row blk z nu v => (.row blk z none nu false, v)
  | .drow z nu v => (.row ⟨CMain.nu20, 0⟩ z none nu false, v)

/-- **The preparation in both shapes** (`s`/`sK` the shape cell, `E`/`K`). -/
def prepZ (F : FCtx) (s sK : Cell) : FClaim → BM (PF × Cell)
  | .e3 cc => zClaimG s F.z F.o cc >>= fun r => pure (.e3 r.1 r.2, r.1.value)
  | .half h parts v => pure (.half h parts true, v)
  | .dhalf h z v =>
    kappa2 F z >>= fun κ => muxD F sK z κ >>= fun mz =>
    g2One κ >>= fun mass => zF2 F (z.getD 20 default) (z.getD 21 default) >>= fun zf =>
    g2Mul mass zf F.z2 >>= fun t =>
    mulAdd .K sK (if h then t.im else t.re) v >>= fun v' =>
    pure (.half h [(mz.1, ⟨22, 0⟩, mz.2.take 22)] false, v')
  | .row blk z nu v => pure (.row blk z none nu true, v)
  | .drow z nu v =>
    kappa2 F z >>= fun κ => muxD F sK z κ >>= fun mz =>
    rowTailG F nu z κ >>= fun tl =>
    mulAdd .E s tl v >>= fun v' =>
    pure (.row ⟨CMain.nu20, 0⟩ mz.2 (some mz.1) nu false, v')

/-- The prepared claims, in order. -/
def prepZs (F : FCtx) (s sK : Cell) : List FClaim → BM (List (PF × Cell))
  | [] => pure []
  | c :: cs => prepZ F s sK c >>= fun r => prepZs F s sK cs >>= fun rs => pure (r :: rs)

/-! ## Terms -/

/-- The `E2` parts' terms of a half (scale `sc`): plain terms (`TC`) and, when regular, pairs (`ZT`). -/
def halfTerms (F : FCtx) (ν xb : Nat) (sc : Cell) (h : Bool) (reg : Bool) :
    List (C2 × Placement × List C2) → Memo6 → BM (Memo6 × List ZT × List TC)
  | [], m => pure (m, [], [])
  | (c, blk, zl) :: ps, m => w6Leaf F xb c zl m >>= fun r =>
    let lf := if h then r.2.2 else r.2.1
    halfTerms F ν xb sc h reg ps r.1 >>= fun rs =>
    if reg then
      pure (rs.1, ⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ ::
        rs.2.1, rs.2.2)
    else pure (rs.1, rs.2.1, ⟨sc, keyOf (selbit blk) ν blk.variableCount, lf⟩ :: rs.2.2)

/-- The terms of one prepared claim (scale `sc`). -/
def pfTerms (F : FCtx) (ν xb : Nat) (sc : Cell) (pf : PF) (memo : Memo) (m6 : Memo6) :
    BM (Memo × Memo6 × List ZT × List TC) :=
  match pf with
  | .e3 cc reg =>
    if reg then regPairs xb F.z F.o sc cc memo >>= fun r => pure (r.1, m6, r.2, [])
    else oneClaim ν xb F.z F.o sc cc memo >>= fun r => pure (r.1, m6, [], r.2)
  | .half h parts reg => halfTerms F ν xb sc h reg parts m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)
  | .row blk z κ nu reg =>
    rowLeafG nu z κ xb F.z F.zk >>= fun lf =>
    if reg then
      pure (memo, m6, [⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩],
        [])
    else pure (memo, m6, [], [⟨sc, keyOf (selbit blk) ν blk.variableCount, lf⟩])

/-- The terms of the prepared claims from index `i` (scale cells `sp + i`). -/
def pfTermsAll (F : FCtx) (ν xb sp : Nat) : Nat → List PF → Memo → Memo6 → BM (List ZT × List TC)
  | _, [], _, _ => pure ([], [])
  | i, pf :: pfs, memo, m6 => pfTerms F ν xb (ec (sp + i)) pf memo m6 >>= fun r =>
    pfTermsAll F ν xb sp (i + 1) pfs r.1 r.2.1 >>= fun rs => pure (r.2.2.1 ++ rs.1, r.2.2.2 ++ rs.2)

/-- **The batched weight, big shape** (`basisG` with the `E2` forms). -/
def basisGF (F : FCtx) (ν : Nat) (pfs : List PF) (sp xb : Nat) : BM Cell :=
  pfTermsAll F ν xb sp 0 pfs [] [] >>= fun r => trieG xb F.z ν r.2

/-- **The batched weight in both shapes** (`basisZ` with the `E2` forms; `s` the `E` shape cell). -/
def basisZF (F : FCtx) (pfs : List PF) (sp xb : Nat) (s : Cell) : BM Cell :=
  pfTermsAll F CMain.nu20 xb sp 0 pfs [] [] >>= fun r =>
  lowsG xb F.z r.1 (keysOf r.1) >>= fun lows =>
  trieG xb F.z CMain.nu20 (lows.map (fun e => (⟨F.o, e.1.1, e.2⟩ : TC)) ++ r.2) >>= fun tb =>
  trieG xb F.z CMain.nu20 (lows.map (fun e => (⟨F.o, e.1.2, e.2⟩ : TC)) ++ r.2) >>= fun ts =>
  muxG s tb ts

/-! ## The opening -/

/-- **`C_main`'s opening at S2GF**: the pin first, then the claims `cs` (V's order); `zon`: both shapes (`mb` the
`E` bits of `n' − 1` for the shape cell, `sK` the shape cell as a `K` cell), else the big shape. -/
def openGF (Cm : SCfg) (zon : Bool) (F : FCtx) (pin : CClaim) (cs : List FClaim) (mb : List Cell) (sK g : Cell) :
    BM Unit :=
  if zon then
    stackGWG Cm (cs.length + 1)
      (do
        let σ ← sigmaG mb F.z
        let pz ← pinZG σ pin
        let ps ← prepZs F σ sK cs
        pure (σ, (PF.e3 pz.1 false, pz.1.value) :: ps))
      (fun w sp => targetG (w.2.map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)) sp F.z)
      (fun w sp xb => do
        let ms ← muxPtG w.1 xb (List.range CMain.nu20)
        let xs ← copiesG ms
        basisZF F (w.2.map (·.1)) sp xs w.1)
      F.z F.o g
  else
    stackGWG Cm (cs.length + 1)
      (pure ((PF.e3 pin false, pin.value) :: cs.map (prepB F)))
      (fun w sp => targetG (w.map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)) sp F.z)
      (fun w sp xb => basisGF F Cm.nu (w.map (·.1)) sp xb)
      F.z F.o g

end Lvm.Q2
