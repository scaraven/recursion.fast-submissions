-- New for lvm6 (WP CLG). The claim gadgets of the level-0 weight cell (CC8's `wBatchG`) that CC8
-- left open: claim 0 (OOD), the sponge claims 16–43 and 45, the typed and mini-bus claims 46–52
-- (FORMAT6 §6.4, §6.5; ORD's order). One `ClaimAt` gadget class per claim form, each instance one
-- generator call; constants of an instance (block bits, selectors) are cells chosen from the
-- instance's own `0`/`1` cells, never row coefficients.
import Lvm6QCFinB
import Lvm6SpProg
import Lvm6TyStmt
import Lvm6QDRelay
import Lvm6MbMid

/-!
# The claim gadgets of the level-0 weight cell (CLG)

Each gadget computes the claim's weight at the cells `x`, for every length of `x` (`ClaimAt`).
Region and lane weights use closed forms, not sums over their words:

* `eq` point claims with constant high bits: **`eqBitsClaimG`** (`eqPt (a ++ bits(w, n))`):
  claims 16 (`cOut_ok`), 17–41 (`cTied_ok`); claim 0 is CC8's `eqClaimG` (`oodClaim_ok`).
* Window/block selectors: **`aboveG p G`** (`eq_above(p)·W(x.take vc)`, `claimAt_above`).
* Region claims: **`regClaimG`**, one `regionG` per region,
  `Σ_{i<2^m} eq(r, b+i)·eq(X, t+i) = eq(r_{≥m}, b/2^m)·eq(X_{≥m}, t/2^m)·eq(r_{<m}, X_{<m})`
  (`regTerm_eq`, every length of `X`): claims 47 (`sigClaim_ok`, σ′ on `C_rec`), 48/49
  (`regClaim_ok` under `RegAff`: com, KS).
* Point claim on `C_rec`: claim 46 (`relayClaim_ok`).
* Mini-bus sum claims: **`mbClaimG`**, one `aboveG`/`eqClaimG` part per committed column
  (`mbClaim_ok`): claims 50–52.
* Lane sums `Σ_{l<N} eq(λ, l)·eq(p ++ bits(t + l, n))`: **`laneSumG`** (`laneClaim_ok`), the sum
  over `l < N` by a carry-free binary recursion on `N` (`ltS`, `ltG`, two products a bit):
  claims 42 (`cY_ok`), 43 (`cIn_ok`), 45 (`cX_ok`).

Claim 44 (the stream words `17x + ℓ`, `x < 7,168`, `ℓ < 17`) is not provided here.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm6.QK

variable {c : Ctx} {M : Mem}

/-! ## `eq` algebra (characteristic 2, every length) -/

theorem eqPt_nil (y : List E2) : eqPt [] y = 1 := by simp [eqPt]

theorem eqPt_nil' (a : List E2) : eqPt a [] = 1 := by simp [eqPt]

theorem eqPt_cons (a b : E2) (x y : List E2) : eqPt (a :: x) (b :: y) = (1 + a + b) * eqPt x y := by
  unfold eqPt
  rw [List.zipWith_cons_cons, List.prod_cons]
  linear_combination (a * b * (List.zipWith (fun r t ↦ r * t + (1 + r) * (1 + t)) x y).prod) * two_E2

theorem eqPt_comm : ∀ (a b : List E2), eqPt a b = eqPt b a
  | [], _ => by simp [eqPt_nil, eqPt_nil']
  | _ :: _, [] => by simp [eqPt_nil, eqPt_nil']
  | a0 :: a, b0 :: b => by rw [eqPt_cons, eqPt_cons, eqPt_comm a b]; ring

theorem eqPt_append : ∀ (a b x : List E2),
    eqPt (a ++ b) x = eqPt a (x.take a.length) * eqPt b (x.drop a.length)
  | [], b, x => by simp [eqPt_nil]
  | _ :: _, _, [] => by simp [eqPt_nil']
  | a0 :: a, b, x0 :: x => by
    rw [List.cons_append, eqPt_cons, eqPt_append a b x, List.length_cons, List.take_succ_cons,
      List.drop_succ_cons, eqPt_cons, mul_assoc]

theorem eqPt_bitsF : ∀ (y : List E2) (w n : ℕ),
    eqPt y (E2V.bitsF w n) = E2V.eqAtF (y.take n) w
  | [], _, _ => by simp [eqPt_nil]
  | _ :: _, _, 0 => by simp [E2V.bitsF, eqPt_nil']
  | y0 :: y, w, n + 1 => by
    rw [E2V.bitsF, eqPt_cons, eqPt_bitsF y (w / 2) n, List.take_succ_cons, E2V.eqAtF]
    split_ifs
    · linear_combination (E2V.eqAtF (y.take n) (w / 2)) * two_E2
    · ring

theorem eqEvalF_eq_eqPt : ∀ (a b : List E2), E2V.eqEvalF a b = eqPt a b
  | [], _ => by simp [E2V.eqEvalF, eqPt_nil]
  | _ :: _, [] => by simp [E2V.eqEvalF, eqPt_nil']
  | a0 :: a, b0 :: b => by rw [E2V.eqEvalF_cons, eqPt_cons, eqEvalF_eq_eqPt a b]

/-- An index inside an aligned block of `2^m`: the low `m` coordinates and the block's bits
(every length of `X`). -/
theorem eqAtF_aligned {m t i : ℕ} (ht : t % 2 ^ m = 0) (hi : i < 2 ^ m) (X : List E2) :
    E2V.eqAtF X (t + i) = E2V.eqAtF (X.take m) i * E2V.eqAtF (X.drop m) (t / 2 ^ m) := by
  rcases le_or_gt m X.length with h | h
  · rw [Mb.eqAtF_block h (Nat.dvd_of_mod_eq_zero ht) hi, Mb.eqAboveG_eq]
  · rw [List.drop_eq_nil_of_le h.le, List.take_of_length_le h.le,
      show E2V.eqAtF ([] : List E2) (t / 2 ^ m) = 1 from rfl, mul_one]
    obtain ⟨k, hk⟩ := (Nat.pow_dvd_pow 2 h.le).trans (Nat.dvd_of_mod_eq_zero ht)
    rw [E2V.eqAtF_mod X (t + i), E2V.eqAtF_mod X i, hk, Nat.add_comm, Nat.add_mul_mod_self_left]

/-- `Σ_{i<2^|ρ|} eq(ρ, i)·eq(Y, i) = eq(ρ, Y)` for `|Y| ≤ |ρ|`. -/
theorem sum_eqAtF_mul_le : ∀ (ρ Y : List E2), Y.length ≤ ρ.length →
    ∑ i ∈ Finset.range (2 ^ ρ.length), E2V.eqAtF ρ i * E2V.eqAtF Y i = E2V.eqEvalF ρ Y
  | [], [], _ => by simp [E2V.eqEvalF, E2V.eqAtF]
  | [], _ :: _, h => by simp at h
  | a :: ρ, [], _ => by
    have h0 : ∀ n, E2V.eqAtF ([] : List E2) n = 1 := fun _ ↦ rfl
    rw [List.length_cons, E2V.sum_cube_succW,
      show E2V.eqEvalF (a :: ρ) ([] : List E2) = E2V.eqEvalF ρ [] by simp [E2V.eqEvalF],
      ← sum_eqAtF_mul_le ρ [] (Nat.zero_le _)]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [E2V.eqAtF_even, E2V.eqAtF_odd]
    simp only [h0]
    linear_combination (a * E2V.eqAtF ρ w) * two_E2
  | a :: ρ, b :: Y, h => by
    simp only [List.length_cons, add_le_add_iff_right] at h
    rw [List.length_cons, E2V.sum_cube_succW, E2V.eqEvalF_cons, ← sum_eqAtF_mul_le ρ Y h,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [E2V.eqAtF_even, E2V.eqAtF_even, E2V.eqAtF_odd, E2V.eqAtF_odd]
    linear_combination (a * b * (E2V.eqAtF ρ w * E2V.eqAtF Y w)) * two_E2

/-! ## Constant bits as cells, `eq` at a constant index -/

/-- The bits of `w` (low first, `n` of them) as the cells `0`/`1`. -/
def bitC (z one : C2) : ℕ → ℕ → List C2
  | _, 0 => []
  | w, n + 1 => (if w % 2 = 1 then one else z) :: bitC z one (w / 2) n

theorem bitC_map {z one : C2} (hz : ev2 M z = 0) (hone : ev2 M one = 1) :
    ∀ w n, (bitC z one w n).map (ev2 M) = (E2V.bitsF w n : List E2)
  | _, 0 => rfl
  | w, n + 1 => by
    rw [bitC, List.map_cons, bitC_map hz hone (w / 2) n, E2V.bitsF]
    split_ifs <;> simp [hz, hone]

/-- `eq(ys, w)` for a constant index `w`: `eqPtG` against `w`'s bit cells. -/
def eqAtG (z one : C2) (ys : List C2) (w : ℕ) : BM C2 := eqPtG z one ys (bitC z one w ys.length)

theorem hs_eqAtG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (ys : List C2) (w : ℕ) :
    Hs c M (eqAtG z one ys w) fun r ↦ ev2 M r = E2V.eqAtF (ys.map (ev2 M)) w :=
  hs_mono (hs_eqPtG hz hone ys _) fun r hr ↦ by
    rw [hr, bitC_map (ev2_of_zero hz) hone, eqPt_bitsF, List.take_of_length_le (by simp)]

/-- An `eq` claim's semantics without `Pre` (CC8's `eqClaimG`). -/
theorem hs_eqClaimG (a x : List C2) (gate : Cell) :
    Hs c M (eqClaimG a x gate) fun r ↦ ev2 M r = eqPt (a.map (ev2 M)) (x.map (ev2 M)) :=
  hs_bind (hs_g2Zero _) fun _ hz ↦ hs_bind (hs_g2Const 1 _) fun one hone ↦
    hs_eqPtG hz (ev2_one' hone) a x

theorem ClaimAt.congr {Pre : Mem → Prop} {cl cl' : Ring.Claim} {G : List C2 → Cell → BM C2}
    (h : ClaimAt Pre cl G) (he : ∀ X, cl.1 X = cl'.1 X) : ClaimAt Pre cl' G :=
  fun c M hP x gate hg ↦ hsA_mono (h c M hP x gate hg) fun o ho ↦ by rw [ho, he]

/-! ## Claim 0 and the sponge point claims 16–41 -/

/-- **Claim 0** (`commit6`'s OOD claim `q̃(z₀) = y₀`): CC8's `eqClaimG` at `z₀`'s cells. -/
theorem oodClaim_ok (Pre : Mem → Prop) (zc : List C2) (z : List E2) (y : E2)
    (h : ∀ M, Pre M → zc.map (ev2 M) = z) : ClaimAt Pre ((fun pt ↦ eqPt z pt), y) (eqClaimG zc) :=
  eqClaim_ok Pre zc z y h

/-- **An `eq` claim with `n` constant high bits `w`** (one instance per claim). -/
def eqBitsClaimG (a : List C2) (w n : ℕ) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦ eqPtG z one (a ++ bitC z one w n) x

theorem eqBitsClaim_ok (Pre : Mem → Prop) (a : List C2) (al : List E2) (w n : ℕ) (v : E2)
    (ha : ∀ M, Pre M → a.map (ev2 M) = al) :
    ClaimAt Pre ((fun pt ↦ eqPt (al ++ E2V.bitsF w n) pt), v) (eqBitsClaimG a w n) := by
  intro c M hP x gate _
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_mono (hs_eqPtG hz (ev2_one' hone) _ x) fun r hr ↦ ?_)
  rw [hr, List.map_append, ha M hP, bitC_map (ev2_of_zero hz) (ev2_one' hone)]

/-- **Claim 16** (`sp̃(r, ϱm) = c_out` on `SP`, slot 35): the point `(r, ϱm)` as cells. -/
theorem cOut_ok (Pre : Mem → Prop) (o : K.SpOut) (rc : List C2)
    (h : ∀ M, Pre M → rc.map (ev2 M) = o.1 ++ o.2.2.1.ϱm) :
    ClaimAt Pre (SP.cOut o) (eqBitsClaimG rc 35 6) :=
  eqBitsClaim_ok Pre rc _ 35 6 _ h

/-- **Claims 17 + ℓ** (`Ỹ_ℓ(r) = v_ℓ`, block `36·64 + ℓ`): the point `r` as cells. -/
theorem cTied_ok (Pre : Mem → Prop) (o : K.SpOut) (l : ℕ) (rc : List C2)
    (h : ∀ M, Pre M → rc.map (ev2 M) = o.1) :
    ClaimAt Pre (SP.cTied o l) (eqBitsClaimG rc (36 * 64 + l) 12) :=
  eqBitsClaim_ok Pre rc _ (36 * 64 + l) 12 _ h

/-! ## Window and block selectors -/

/-- **`eq_above(p)·W(x.take vc)`**: the selector against the bits of `p.index / 2^vc`, then the
inner gadget on the block's coordinates. -/
def aboveG (p : LeanVM.Protocol.Verifier.Placement) (G : List C2 → Cell → BM C2) (x : List C2)
    (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦
    eqAtG z one (x.drop p.variableCount) (p.index / 2 ^ p.variableCount) >>= fun s ↦
      G (x.take p.variableCount) gate >>= fun i ↦ g2Mul s i z

theorem hsA_aboveG (p : LeanVM.Protocol.Verifier.Placement) {G : List C2 → Cell → BM C2}
    {w : List E2 → E2} (x : List C2) {gate : Cell}
    (hG : HsA c M (G (x.take p.variableCount) gate) fun o ↦
      ev2 M o = w ((x.take p.variableCount).map (ev2 M))) :
    HsA c M (aboveG p G x gate) fun o ↦
      ev2 M o = Mb.eqAboveG p (x.map (ev2 M)) * w ((x.map (ev2 M)).take p.variableCount) := by
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ hsA_bind (hsA_of_hs (hs_g2Const 1 z))
    fun one hone ↦ hsA_bind (hsA_of_hs (hs_eqAtG hz (ev2_one' hone) _ _)) fun s hs ↦
      hsA_bind hG fun i hi ↦ hsA_of_hs (hs_mono (hs_g2Mul s i z) fun o ho ↦ ?_)
  obtain ⟨vc, idx⟩ := p
  rw [ev2_mul ho, ev2_of_zero hz, add_zero, hs, hi, Mb.eqAboveG_eq, List.map_drop, List.map_take]

/-- **`ClaimAt` under a selector** (`BClaimG.onStack`, `recClaim`). -/
theorem claimAt_above {Pre : Mem → Prop} (p : LeanVM.Protocol.Verifier.Placement)
    {w : List E2 → E2} {v v' : E2} {G : List C2 → Cell → BM C2} (hG : ClaimAt Pre (w, v) G) :
    ClaimAt Pre ((fun X ↦ Mb.eqAboveG p X * w (X.take p.variableCount)), v') (aboveG p G) :=
  fun c M hP x gate hg ↦ hsA_aboveG p x (hG c M hP _ gate hg)

/-! ## Claim 46: the relayout's point claim on `C_rec` -/

/-- Claim 46's gadget: `C_rec`'s window, the block `⟨19, 0⟩`, `eq(r, ·)`. -/
def relayClaimG (rrc : List C2) : List C2 → Cell → BM C2 :=
  aboveG ⟨19, Ty.recOff⟩ (aboveG ⟨Ty.relayRounds, 0⟩ (eqClaimG rrc))

/-- **Claim 46** (FORMAT6 §6.4 claim 1): the point `r` as cells. -/
theorem relayClaim_ok (Pre : Mem → Prop) (rrc : List C2) (rr : List E2) (vR : E2)
    (h : ∀ M, Pre M → rrc.map (ev2 M) = rr) :
    ClaimAt Pre (Ty.recClaim ((Mb.BClaimG.point ⟨Ty.relayRounds, 0⟩ rr vR).onStack))
      (relayClaimG rrc) :=
  claimAt_above (v := vR) _ (claimAt_above (v := vR) _
    ((eqClaim_ok Pre rrc rr vR h).congr fun X ↦ (eqEvalF_eq_eqPt rr X).symm))

/-! ## Region claims (47–49) -/

/-- One aligned region and its target: `Σ_{i<2^m} eq(r, b+i)·eq(X, t+i)` in closed form. -/
theorem regTerm_eq (r X : List E2) {lg b t : ℕ} (w : ℕ → ℕ) (hb : b % 2 ^ lg = 0)
    (ht : t % 2 ^ lg = 0) (hw : ∀ i < 2 ^ lg, w (b + i) = t + i) (hr : lg ≤ r.length) :
    ((List.range (2 ^ lg)).map fun i ↦ E2V.eqAtF r (b + i) * E2V.eqAtF X (w (b + i))).sum =
      E2V.eqAtF (r.drop lg) (b / 2 ^ lg) * E2V.eqAtF (X.drop lg) (t / 2 ^ lg) *
        E2V.eqEvalF (r.take lg) (X.take lg) := by
  have hl : (r.take lg).length = lg := by simp [hr]
  have hs := sum_eqAtF_mul_le (r.take lg) (X.take lg) (by rw [hl]; exact List.length_take_le _ _)
  rw [hl] at hs
  rw [lsum_range]
  have key : ∀ i ∈ Finset.range (2 ^ lg), E2V.eqAtF r (b + i) * E2V.eqAtF X (w (b + i)) =
      E2V.eqAtF (r.drop lg) (b / 2 ^ lg) * E2V.eqAtF (X.drop lg) (t / 2 ^ lg) *
        (E2V.eqAtF (r.take lg) i * E2V.eqAtF (X.take lg) i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hw i hi', eqAtF_aligned hb hi', eqAtF_aligned ht hi']
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, hs]

/-- **The regions of a source and their targets** `(region, target base)`: the source's regions,
aligned, the map affine on each. -/
def RegAff (Ti : Ty.TInst6) (s : Lvm.Typed.YSrc) (w : ℕ → ℕ)
    (regs : List (Lvm.Typed.YReg × ℕ)) : Prop :=
  (Ti.lay.yregs.filter fun r ↦ r.src == s) = regs.map Prod.fst ∧
    ∀ p ∈ regs, p.1.base % 2 ^ p.1.log = 0 ∧ p.2 % 2 ^ p.1.log = 0 ∧
      ∀ i < 2 ^ p.1.log, w (p.1.base + i) = p.2 + i

/-- A region's closed-form term, the region as `(log, base, target)`. -/
noncomputable def regT (r X : List E2) (q : ℕ × ℕ × ℕ) : E2 :=
  E2V.eqAtF (r.drop q.1) (q.2.1 / 2 ^ q.1) * E2V.eqAtF (X.drop q.1) (q.2.2 / 2 ^ q.1) *
    E2V.eqEvalF (r.take q.1) (X.take q.1)

/-- The static description of the regions. -/
def regQs (regs : List (Lvm.Typed.YReg × ℕ)) : List (ℕ × ℕ × ℕ) :=
  regs.map fun p ↦ (p.1.log, p.1.base, p.2)

theorem regClaimE_eq {Ti : Ty.TInst6} {s : Lvm.Typed.YSrc} {w : ℕ → ℕ}
    {regs : List (Lvm.Typed.YReg × ℕ)} (hA : RegAff Ti s w regs) {r : List E2}
    (hr : ∀ p ∈ regs, p.1.log ≤ r.length) (v : E2) (X : List E2) :
    (Ty.regClaimE Ti s w r v).1 X = ((regQs regs).map (regT r X)).sum := by
  obtain ⟨hf, ha⟩ := hA
  show Ty.regSumT Ti (fun s' ↦ s' == s) (fun y ↦ E2V.eqAtF X (w y)) r = _
  unfold Ty.regSumT
  rw [QD.regSumW_filter, hf, List.map_map, regQs, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp ↦ ?_
  obtain ⟨hb, ht, hw⟩ := ha p hp
  exact regTerm_eq r X w hb ht hw (hr p hp)

/-- **One region** (one instance per region): `acc + eq(r_{≥m}, b/2^m)·eq(x_{≥m}, t/2^m)·eq(r_{<m},
x_{<m})`. -/
def regionG (z one acc : C2) (rc : List C2) (q : ℕ × ℕ × ℕ) (x : List C2) : BM C2 :=
  eqAtG z one (rc.drop q.1) (q.2.1 / 2 ^ q.1) >>= fun s1 ↦
    eqAtG z one (x.drop q.1) (q.2.2 / 2 ^ q.1) >>= fun s2 ↦
      eqPtG z one (rc.take q.1) (x.take q.1) >>= fun s3 ↦ g2Mul s1 s2 z >>= fun u ↦ g2Mul u s3 acc

/-- The regions, one `regionG` each. -/
def regsG (z one : C2) (rc : List C2) : C2 → List (ℕ × ℕ × ℕ) → List C2 → BM C2
  | acc, [], _ => pure acc
  | acc, q :: qs, x => regionG z one acc rc q x >>= fun a ↦ regsG z one rc a qs x

theorem hs_regsG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (rc x : List C2) :
    ∀ (qs : List (ℕ × ℕ × ℕ)) (acc : C2), Hs c M (regsG z one rc acc qs x) fun o ↦
      ev2 M o = ev2 M acc + (qs.map (regT (rc.map (ev2 M)) (x.map (ev2 M)))).sum
  | [], acc => hs_pure (by simp)
  | q :: qs, acc => by
    refine hs_bind (hs_bind (hs_eqAtG hz hone _ _) fun s1 h1 ↦ hs_bind (hs_eqAtG hz hone _ _)
      fun s2 h2 ↦ hs_bind (hs_eqPtG hz hone _ _) fun s3 h3 ↦ hs_bind (hs_g2Mul s1 s2 z) fun u hu ↦
        hs_mono (hs_g2Mul u s3 acc) fun a ha ↦ (?_ : ev2 M a = ev2 M acc +
          regT (rc.map (ev2 M)) (x.map (ev2 M)) q)) fun a ha ↦
      hs_mono (hs_regsG hz hone rc x qs a) fun o ho ↦ ?_
    · rw [ev2_mul ha, ev2_mul hu, ev2_of_zero hz, add_zero, h1, h2, h3, regT,
        ← eqEvalF_eq_eqPt, List.map_drop, List.map_drop, List.map_take, List.map_take]
      ring
    · rw [ho, ha, List.map_cons, List.sum_cons, add_assoc]

/-- **A region claim's gadget**: `0`/`1` cells, then the regions. -/
def regClaimG (rc : List C2) (qs : List (ℕ × ℕ × ℕ)) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦ regsG z one rc z qs x

/-- **`ClaimAt` for a region claim** (`regClaimE`) whose regions are affine (`RegAff`). -/
theorem regClaim_ok (Pre : Mem → Prop) (Ti : Ty.TInst6) (s : Lvm.Typed.YSrc) (w : ℕ → ℕ)
    (regs : List (Lvm.Typed.YReg × ℕ)) (hA : RegAff Ti s w regs) (rc : List C2) (ry : List E2)
    (v : E2) (hr : ∀ p ∈ regs, p.1.log ≤ ry.length) (h : ∀ M, Pre M → rc.map (ev2 M) = ry) :
    ClaimAt Pre (Ty.regClaimE Ti s w ry v) (regClaimG rc (regQs regs)) := by
  intro c M hP x gate _
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_mono (hs_regsG hz (ev2_one' hone) rc x _ z) fun o ho ↦ ?_)
  rw [ho, ev2_of_zero hz, zero_add, regClaimE_eq hA hr, h M hP]

/-- **Claim 47** (σ′ on `C_rec`, FORMAT6 §6.4 claim 2): one region of `2^11` words at `bg`,
targets `sB + j`. -/
def sigClaimG (rc : List C2) (bg : ℕ) : List C2 → Cell → BM C2 :=
  aboveG ⟨19, Ty.recOff⟩ (regClaimG rc [(QD.sigLog, bg, QD.sB)])

theorem sigClaim_ok (Pre : Mem → Prop) (Ti : Ty.TInst6) (hok : Ti.Ok) (bg : ℕ)
    (hf : (Ti.lay.yregs.filter fun r ↦ r.src == .sigma) = [⟨bg, QD.sigLog, .sigma⟩])
    (hw : ∀ j < 2 ^ QD.sigLog, Ti.sigmaW (bg + j) = QD.sB + j) (rc : List C2) (ry : List E2)
    (v : E2) (hry : QD.sigLog ≤ ry.length) (h : ∀ M, Pre M → rc.map (ev2 M) = ry) :
    ClaimAt Pre (Ty.recClaim (Ty.regClaimE Ti .sigma Ti.sigmaW ry v)) (sigClaimG rc bg) := by
  have hmem : (⟨bg, QD.sigLog, .sigma⟩ : Lvm.Typed.YReg) ∈ Ti.lay.yregs := by
    have : (⟨bg, QD.sigLog, .sigma⟩ : Lvm.Typed.YReg) ∈
        Ti.lay.yregs.filter (fun r ↦ r.src == .sigma) := by
      rw [hf]; exact List.mem_singleton_self _
    exact (List.mem_filter.mp this).1
  have hA : RegAff Ti .sigma Ti.sigmaW [(⟨bg, QD.sigLog, .sigma⟩, QD.sB)] := by
    refine ⟨by rw [hf]; rfl, fun p hp ↦ ?_⟩
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨QD.ok_aligned hok _ hmem, show QD.sB % 2 ^ QD.sigLog = 0 by decide, hw⟩
  exact claimAt_above (v := v) _ (regClaim_ok Pre Ti .sigma Ti.sigmaW _ hA rc ry v
    (fun p hp ↦ by rw [List.mem_singleton] at hp; subst hp; exact hry) h)

/-! ## The mini-bus sum claims (50–52) -/

/-- The parts of a sum claim, one `aboveG`/`eqClaimG` instance per committed column: coefficient
cell, block, point cells. -/
def partsG : C2 → List (C2 × LeanVM.Protocol.Verifier.Placement × List C2) → List C2 → Cell →
    BM C2
  | acc, [], _, _ => pure acc
  | acc, q :: qs, x, gate => aboveG q.2.1 (eqClaimG q.2.2) x gate >>= fun t ↦
      g2Mul q.1 t acc >>= fun a ↦ partsG a qs x gate

/-- The parts' values. -/
def partsV (M : Mem) (qs : List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) :
    List (E2 × LeanVM.Protocol.Verifier.Placement × List E2) :=
  qs.map fun q ↦ (ev2 M q.1, q.2.1, q.2.2.map (ev2 M))

theorem partsV_cons (q : C2 × LeanVM.Protocol.Verifier.Placement × List C2)
    (qs : List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) :
    partsV M (q :: qs) = (ev2 M q.1, q.2.1, q.2.2.map (ev2 M)) :: partsV M qs := rfl

theorem hsA_partsG (x : List C2) {gate : Cell} : ∀ (qs : List (C2 × LeanVM.Protocol.Verifier.Placement ×
    List C2)) (acc : C2), HsA c M (partsG acc qs x gate) fun o ↦ ev2 M o = ev2 M acc +
      ((partsV M qs).map fun p ↦ p.1 * Mb.eqAboveG p.2.1 (x.map (ev2 M)) *
        E2V.eqEvalF p.2.2 ((x.map (ev2 M)).take p.2.1.variableCount)).sum
  | [], acc => hsA_pure (by simp [partsV])
  | q :: qs, acc => by
    refine hsA_bind (hsA_aboveG q.2.1 x (w := fun X ↦ eqPt (q.2.2.map (ev2 M)) X)
      (hsA_of_hs (hs_eqClaimG _ _ _))) fun t ht ↦ hsA_bind (hsA_of_hs (hs_g2Mul q.1 t acc))
        fun a ha ↦ hsA_mono (hsA_partsG x qs a) fun o ho ↦ ?_
    rw [ho, ev2_mul ha, ht, partsV_cons, List.map_cons, List.sum_cons, eqEvalF_eq_eqPt]
    ring

/-- **A mini-bus claim's gadget** (`sumClaimG ν parts` on `C_main`'s window `⟨ν, 0⟩`). -/
def mbClaimG (nu : ℕ) (qs : List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) :
    List C2 → Cell → BM C2 :=
  aboveG ⟨nu, 0⟩ fun x gate ↦ g2Zero ⟨gate, gate⟩ >>= fun z ↦ partsG z qs x gate

/-- **Claims 50–52** (`mbClaimsG`'s push, pull, count, each `sumClaimG ν (mbPartsG …) …`): the
parts' coefficients and points as cells. -/
theorem mbClaim_ok (Pre : Mem → Prop) (nu : ℕ)
    (qs : List (C2 × LeanVM.Protocol.Verifier.Placement × List C2))
    (parts : List (E2 × LeanVM.Protocol.Verifier.Placement × List E2)) (v : E2)
    (h : ∀ M, Pre M → partsV M qs = parts) :
    ClaimAt Pre ((Mb.sumClaimG nu parts v).onStack) (mbClaimG nu qs) := by
  refine claimAt_above (v := v) _ fun c M hP x gate _ ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ hsA_mono (hsA_partsG x qs z) fun o ho ↦ ?_
  rw [ho, ev2_of_zero hz, zero_add, h M hP]
  show _ = E2V.sumF _
  rw [E2V.sumF_eq_sum]

/-! ## Lane sums (42, 43, 45): `Σ_{l<N} eq(λ, l)·eq(p ++ bits(t + l, n), ·)` -/

/-- The product `Π_i f_i(l_i)` of per-coordinate pairs `(f_i(0), f_i(1))`. -/
def termP : List (E2 × E2) → ℕ → E2
  | [], _ => 1
  | f :: fs, l => (if l % 2 = 1 then f.2 else f.1) * termP fs (l / 2)

/-- The pairs of `eq(a, ·)·eq(y, ·)` per coordinate (a missing coordinate is a factor `1`). -/
def fpE : List E2 → List E2 → List (E2 × E2)
  | a :: as, y :: ys => ((1 + a) * (1 + y), a * y) :: fpE as ys
  | a :: as, [] => (1 + a, a) :: fpE as []
  | [], ys => ys.map fun y ↦ (1 + y, y)

theorem termP_ones : ∀ (y : List E2) (l : ℕ), termP (y.map fun y ↦ (1 + y, y)) l = E2V.eqAtF y l
  | [], _ => rfl
  | y0 :: y, l => by
    rw [List.map_cons, termP, termP_ones y]
    rfl

theorem termP_fpE : ∀ (a y : List E2) (l : ℕ),
    termP (fpE a y) l = E2V.eqAtF a l * E2V.eqAtF y l
  | a0 :: a, y0 :: y, l => by
    simp only [fpE, termP, termP_fpE a y, E2V.eqAtF]
    split_ifs <;> ring
  | a0 :: a, [], l => by
    simp only [fpE, termP, termP_fpE a [], E2V.eqAtF]
    split_ifs <;> ring
  | [], y, l => by rw [fpE, termP_ones]; exact (one_mul _).symm

/-- `Σ_{l<N} Π_i f_i(l_i)`. -/
noncomputable def ltS (fs : List (E2 × E2)) (N : ℕ) : E2 := ∑ l ∈ Finset.range N, termP fs l

theorem natCast_E2 (N : ℕ) : (N : E2) = if N % 2 = 1 then 1 else 0 := by
  conv_lhs => rw [← Nat.div_add_mod N 2]
  push_cast
  rw [two_E2, zero_mul, zero_add]
  rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h]

theorem ltS_nil (N : ℕ) : ltS [] N = if N % 2 = 1 then 1 else 0 := by
  rw [ltS, ← natCast_E2]
  simp [termP]

theorem ltS_cons (f : E2 × E2) (fs : List (E2 × E2)) (N : ℕ) :
    ltS (f :: fs) N = (f.1 + f.2) * ltS fs (N / 2) +
      if N % 2 = 1 then f.1 * termP fs (N / 2) else 0 := by
  have hev : ∀ n, ∑ l ∈ Finset.range (2 * n), termP (f :: fs) l = (f.1 + f.2) * ltS fs n := by
    intro n
    rw [E2V.sum_range_two_mulW, ltS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [termP]
    rw [if_neg (by omega), if_pos (by omega), show 2 * w / 2 = w by omega,
      show (2 * w + 1) / 2 = w by omega]
    ring
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, N = 2 * n := ⟨N / 2, by omega⟩
    rw [ltS, hev, if_neg (by omega), add_zero, show 2 * n / 2 = n by omega]
  · obtain ⟨n, rfl⟩ : ∃ n, N = 2 * n + 1 := ⟨N / 2, by omega⟩
    rw [ltS, Finset.sum_range_succ, hev, if_pos h, show (2 * n + 1) / 2 = n by omega]
    simp only [termP]
    rw [if_neg (by omega), show 2 * n / 2 = n by omega]

/-- The pairs' cells: `(1+a)(1+y)`, `a·y` (or `1+a`, `a` when `y` is missing, and so on). -/
def fpG (z : C2) : List C2 → List C2 → BM (List (C2 × C2))
  | a :: as, y :: ys => g2One a >>= fun a1 ↦ g2One y >>= fun y1 ↦ g2Mul a1 y1 z >>= fun p0 ↦
      g2Mul a y z >>= fun p1 ↦ fpG z as ys >>= fun r ↦ pure ((p0, p1) :: r)
  | a :: as, [] => g2One a >>= fun a1 ↦ fpG z as [] >>= fun r ↦ pure ((a1, a) :: r)
  | [], ys => mapB (fun y ↦ g2One y >>= fun y1 ↦ pure (y1, y)) ys

/-- The pairs' values. -/
def pairsV (M : Mem) (fs : List (C2 × C2)) : List (E2 × E2) := fs.map fun f ↦ (ev2 M f.1, ev2 M f.2)

theorem pairsV_cons (f : C2 × C2) (fs : List (C2 × C2)) :
    pairsV M (f :: fs) = (ev2 M f.1, ev2 M f.2) :: pairsV M fs := rfl

theorem pairsV_nil : pairsV M [] = [] := rfl

theorem ev2_onePlus {r a : C2} (h : r.val M = 1 + a.val M) : ev2 M r = 1 + ev2 M a := by
  simp [ev2, h, FE2.toE2_add]

theorem hs_onesG : ∀ (ys : List C2), Hs c M (mapB (fun y ↦ g2One y >>= fun y1 ↦ pure (y1, y)) ys)
    fun fs ↦ pairsV M fs = (ys.map (ev2 M)).map fun y ↦ (1 + y, y)
  | [] => hs_pure rfl
  | y :: ys => by
    refine hs_bind (P := fun b : C2 × C2 ↦ ev2 M b.1 = 1 + ev2 M y ∧ b.2 = y)
      (hs_bind (hs_g2One y) fun y1 hy1 ↦ hs_pure ⟨ev2_onePlus hy1, rfl⟩) fun b hb ↦
        hs_bind (hs_onesG ys) fun r hr ↦ hs_pure ?_
    rw [pairsV_cons, hr, hb.1, hb.2, List.map_cons, List.map_cons]

theorem hs_fpG {z : C2} (hz : z.val M = 0) : ∀ (as ys : List C2),
    Hs c M (fpG z as ys) fun fs ↦ pairsV M fs = fpE (as.map (ev2 M)) (ys.map (ev2 M))
  | a :: as, y :: ys => by
    rw [fpG]
    exact hs_bind (hs_g2One a) fun a1 ha1 ↦ hs_bind (hs_g2One y) fun y1 hy1 ↦
      hs_bind (hs_g2Mul a1 y1 z) fun p0 hp0 ↦ hs_bind (hs_g2Mul a y z) fun p1 hp1 ↦
        hs_bind (hs_fpG hz as ys) fun r hr ↦ hs_pure (by
          rw [pairsV_cons, hr, ev2_mul hp0, ev2_mul hp1, ev2_onePlus ha1, ev2_onePlus hy1,
            ev2_of_zero hz, add_zero, add_zero, List.map_cons, List.map_cons, fpE])
  | a :: as, [] => by
    rw [fpG]
    exact hs_bind (hs_g2One a) fun a1 ha1 ↦ hs_bind (hs_fpG hz as []) fun r hr ↦ hs_pure (by
      rw [pairsV_cons, hr, ev2_onePlus ha1, List.map_cons, List.map_nil, fpE])
  | [], ys => by
    rw [fpG]
    exact hs_mono (hs_onesG ys) fun fs h ↦ by rw [h, List.map_nil, fpE]

/-- **`Σ_{l<N} Π f_i(l_i)` and `Π f_i(N_i)`**, by the bits of `N` (low first): two or three
products a coordinate. -/
def ltG (z one : C2) : List (C2 × C2) → ℕ → BM (C2 × C2)
  | [], N => pure (if N % 2 = 1 then one else z, one)
  | f :: fs, N => ltG z one fs (N / 2) >>= fun tp ↦ g2Add f.1 f.2 >>= fun s ↦
      g2Mul s tp.1 z >>= fun t0 ↦
        if N % 2 = 1 then g2Mul f.1 tp.2 t0 >>= fun t ↦ g2Mul f.2 tp.2 z >>= fun p ↦ pure (t, p)
        else g2Mul f.1 tp.2 z >>= fun p ↦ pure (t0, p)

theorem hs_ltG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) :
    ∀ (fs : List (C2 × C2)) (N : ℕ), Hs c M (ltG z one fs N) fun tp ↦
      ev2 M tp.1 = ltS (pairsV M fs) N ∧ ev2 M tp.2 = termP (pairsV M fs) N
  | [], N => hs_pure (by
      rw [pairsV_nil, ltS_nil]
      refine ⟨?_, by rw [hone]; rfl⟩
      split_ifs <;> simp [hone, ev2_of_zero hz])
  | f :: fs, N => by
    refine hs_bind (hs_ltG hz hone fs (N / 2)) fun tp htp ↦ hs_bind (hs_g2Add f.1 f.2) fun s hs ↦
      hs_bind (hs_g2Mul s tp.1 z) fun t0 ht0 ↦ ?_
    have e0 : ev2 M t0 = (ev2 M f.1 + ev2 M f.2) * ltS (pairsV M fs) (N / 2) := by
      rw [ev2_mul ht0, ev2_add hs, htp.1, ev2_of_zero hz, add_zero]
    by_cases hN : N % 2 = 1
    · simp only [hN, if_true]
      exact hs_bind (hs_g2Mul f.1 tp.2 t0) fun t ht ↦ hs_bind (hs_g2Mul f.2 tp.2 z) fun p hp ↦
        hs_pure ⟨by rw [ev2_mul ht, e0, htp.2, pairsV_cons, ltS_cons, if_pos hN]; ring,
          by rw [ev2_mul hp, htp.2, ev2_of_zero hz, add_zero, pairsV_cons, termP, if_pos hN]⟩
    · simp only [hN, if_false]
      exact hs_bind (hs_g2Mul f.1 tp.2 z) fun p hp ↦
        hs_pure ⟨by rw [e0, pairsV_cons, ltS_cons, if_neg hN, add_zero],
          by rw [ev2_mul hp, htp.2, ev2_of_zero hz, add_zero, pairsV_cons, termP, if_neg hN]⟩

/-- **The lane-sum weight in closed form**: `Σ_{l<N} eq(λ, l)·eq(p ++ bits(t + l, n), pt)` for
`t` aligned to `2^m ≥ N`. -/
theorem laneW_eq (lam p : List E2) {N t m : ℕ} (n : ℕ) (ht : t % 2 ^ m = 0) (hN : N ≤ 2 ^ m)
    (pt : List E2) :
    ∑ l ∈ Finset.range N, E2V.eqAtF lam l * eqPt (p ++ E2V.bitsF (t + l) n) pt =
      eqPt p (pt.take p.length) * E2V.eqAtF (((pt.drop p.length).take n).drop m) (t / 2 ^ m) *
        ltS (fpE lam (((pt.drop p.length).take n).take m)) N := by
  rw [ltS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' : l < 2 ^ m := lt_of_lt_of_le (Finset.mem_range.mp hl) hN
  rw [eqPt_append, eqPt_comm (E2V.bitsF (t + l) n), eqPt_bitsF, eqAtF_aligned ht hl', termP_fpE]
  ring

/-- **A lane-sum claim's gadget** (one instance per claim): `eq(p, ·)` on the first `|p|`
coordinates, the block bits `t/2^m`, then `ltG` on the lane coordinates. -/
def laneSumG (lc pc : List C2) (N t m n : ℕ) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦
    eqPtG z one pc (x.take pc.length) >>= fun e1 ↦
      eqAtG z one (((x.drop pc.length).take n).drop m) (t / 2 ^ m) >>= fun e2 ↦
        fpG z lc (((x.drop pc.length).take n).take m) >>= fun fs ↦ ltG z one fs N >>= fun tp ↦
          g2Mul e1 e2 z >>= fun u ↦ g2Mul u tp.1 z

/-- **`ClaimAt` for a lane-sum claim**: `λ` and `p` as cells. -/
theorem laneClaim_ok (Pre : Mem → Prop) (lc pc : List C2) (lam p : List E2) {N t m : ℕ} (n : ℕ)
    (v : E2) (ht : t % 2 ^ m = 0) (hN : N ≤ 2 ^ m)
    (h : ∀ M, Pre M → lc.map (ev2 M) = lam ∧ pc.map (ev2 M) = p) :
    ClaimAt Pre ((fun pt ↦ ∑ l ∈ Finset.range N,
      E2V.eqAtF lam l * eqPt (p ++ E2V.bitsF (t + l) n) pt), v) (laneSumG lc pc N t m n) := by
  intro c M hP x gate _
  obtain ⟨hl, hp⟩ := h M hP
  have hlen : pc.length = p.length := by rw [← hp, List.length_map]
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_bind (hs_eqPtG hz (ev2_one' hone) _ _) fun e1 h1 ↦
      hs_bind (hs_eqAtG hz (ev2_one' hone) _ _) fun e2 h2 ↦ hs_bind (hs_fpG hz _ _) fun fs hfs ↦
        hs_bind (hs_ltG hz (ev2_one' hone) fs N) fun tp htp ↦ hs_bind (hs_g2Mul e1 e2 z)
          fun u hu ↦ hs_mono (hs_g2Mul u tp.1 z) fun o ho ↦ ?_)
  show ev2 M o = ∑ l ∈ Finset.range N, E2V.eqAtF lam l * eqPt (p ++ E2V.bitsF (t + l) n)
    (x.map (ev2 M))
  rw [laneW_eq lam p n ht hN, ev2_mul ho, ev2_mul hu, ev2_of_zero hz, add_zero, add_zero, h1, h2,
    htp.1, hfs, hl, hp, ← hlen]
  simp only [List.map_take, List.map_drop]

/-- **Claim 42** (`Σ_{ℓ<25} eq(λ, ℓ)·Ỹ_ℓ(ρ')`, blocks `36·64 + ℓ`). -/
theorem cY_ok (Pre : Mem → Prop) (lk : SP.LinkOut) (lc pc : List C2)
    (h : ∀ M, Pre M → lc.map (ev2 M) = lk.1.drop 13 ∧ pc.map (ev2 M) = lk.2.1.1) :
    ClaimAt Pre (SP.cY lk) (laneSumG lc pc 25 (36 * 64) 6 12) :=
  laneClaim_ok Pre lc pc _ _ 12 _ (by norm_num) (by norm_num) h

/-- **Claim 43** (`Σ_{ℓ<25} eq(λ, ℓ)·sp̃(ρ', slot ℓ)`, blocks `35·64 + ℓ`). -/
theorem cIn_ok (Pre : Mem → Prop) (lk : SP.LinkOut) (lc pc : List C2)
    (h : ∀ M, Pre M → lc.map (ev2 M) = lk.1.drop 13 ∧ pc.map (ev2 M) = lk.2.1.1) :
    ClaimAt Pre (SP.cIn lk) (laneSumG lc pc 25 (35 * 64) 6 12) :=
  laneClaim_ok Pre lc pc _ _ 12 _ (by norm_num) (by norm_num) h

/-- **Claim 45** (`Σ_{ℓ<17} eq(λ, ℓ)·X̃_ℓ(ρ'_{<10})`, blocks `37·2^9 + ℓ` of `2^10` words). -/
theorem cX_ok (Pre : Mem → Prop) (lk : SP.LinkOut) (lc pc : List C2)
    (h : ∀ M, Pre M → lc.map (ev2 M) = lk.1.drop 13 ∧ pc.map (ev2 M) = lk.2.1.1.take 10) :
    ClaimAt Pre (SP.cX lk) (laneSumG lc pc 17 (37 * 2 ^ 9) 9 15) :=
  laneClaim_ok Pre lc pc _ _ 15 _ (by norm_num) (by norm_num) h

end Lvm6.QC
