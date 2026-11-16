-- New for lvm2 S2GT (GT-C2): Q_arith at S2GT, the circuit side of statement 10's sub-items: the mini-bus record of a
-- guarded configuration (10e, `miniC`), and blob GT's typed claims standing for V_S's `typedClaimsND` (10d,
-- `typed_relT`: the `E2` claims as their re/im halves, the mini-bus's table claims at `E3`).
import LvmE2QTypedT
import LvmE2QInstT
import LvmE2QHarF
import LvmE2TV

/-!
# Q_arith at S2GT: the mini-bus record and the typed claims

* **`miniC`** (10e): on a guarded configuration (`NodeGC`), the mini-bus's tables are sumcheck tables and the
  circuit's static data (`tdataOf`) has the record's table shapes, rounds, depth and fixed list (`miniF20` generic in
  the configuration; at S2GT `miniG20`, in `LvmS2GTStmtC`).
* `hs_eqConst2`, `hs_regParts2`: a region's selector at `E2` is `hiWG`; the region parts by value.
* `affWD_parts`: V_S's region weight (`affWD`) is coordinate `h` of the parts' `sumW6D` on V's regions.
* **`typed_relT`** (10d): `typedClaimsGT`'s claims stand for `typedClaimsND ++ zeroTails (table claims)` under
  `FRelZ`, claim for claim (each `E2` claim's halves re then im; the table claims at `E3`, tail `0`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.QTyped Lvm.Q2 Lvm.QShape
open Lvm.E2T (TNatT affWD regClaimsND typedClaimsND hiWG)

variable {c : Ctx} {M : Mem}

/-! ## 10e: the mini-bus record of a guarded configuration -/

/-- **The mini-bus record** (`miniF20` at any guarded configuration): the tables are all sumcheck tables, the
circuit's tables, rounds, depth and fixed list are the record's. -/
theorem miniC {C : QCfg} {B nPub : ℕ} {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TypedV.TNat}
    (S : NodeGC C B nPub F Q tl N) : Lvm.M3.sumcheckTabs N.mbT = N.mbT ∧
    (tdataOf C F).mbS = N.mbT.map Lvm.M3.Tab.shape ∧ (tdataOf C F).mbR = C.p.tableRounds ∧
    (tdataOf C F).mbD = C.p.busDepth ∧ Lvm.Har.FixListed N.mbT (tdataOf C F).mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf C F) = mbTOf C F := Lvm.Har.mbT_sumcheck C _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm ⊢
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨t1, t2, t3, t4⟩ := Lvm.Har.tdataOf_mb C F
  rw [t1, t2, t3, t4, hR, hD]
  exact ⟨hsc, rfl, rfl, rfl, Lvm.Har.mbT_fix C _ _ _⟩

/-! ## 10d: the typed claims at `E2` -/

/-- **`eq(r, b)` at `E2`** (`eqConst2`): `E2V.eqAtF` of the point's values, a `K`-celled value. -/
theorem hs_eqConst2 {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (hoK : KC2 o2) :
    ∀ (rs : List C2) (b : ℕ), Hs c M (eqConst2 z2 o2 rs b)
      (fun r => KC2 r ∧ r.val M = E2V.eqAtF (rs.map (C2.val M)) b)
  | [], _ => hs_pure ⟨hoK, by rw [ho]; rfl⟩
  | r :: rs, b => by
    rw [eqConst2]
    refine hs_bind (hs_eqConst2 hz ho hoK rs (b / 2)) fun t ⟨_, ht⟩ => ?_
    by_cases hb : b % 2 = 1
    · rw [if_pos hb]
      refine hs_and (g2Mul_K _ _ _) (hs_mono (hs_g2Mul _ _ _) fun x hx => ?_)
      rw [hx, hz, add_zero, ht, List.map_cons, E2V.eqAtF, if_pos hb, mul_comm]
    · rw [if_neg hb]
      refine hs_bind (hs_g2One r) fun u hu => hs_and (g2Mul_K _ _ _) (hs_mono (hs_g2Mul _ _ _) fun x hx => ?_)
      rw [hx, hz, add_zero, ht, hu, List.map_cons, E2V.eqAtF, if_neg hb, mul_comm]

/-- **A region family's parts at `E2`** (`regParts2`): `K`-celled selectors `hiWG(r_y)`, the blocks
`⟨log, off⟩`, the points `r_y^{< log}`. -/
theorem hs_regParts2 {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (hoK : KC2 o2) (ry : List C2) :
    ∀ rs : List TReg, Hs c M (regParts2 z2 o2 rs ry) (fun ps => (∀ e ∈ ps, KC2 e.1) ∧
      ps.map (·.2) = rs.map (fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log)) ∧
      partsV M ps = rs.map fun R => (hiWG (ry.map (C2.val M)) R.log R.base, (⟨R.log, R.off⟩ : Placement),
        (ry.map (C2.val M)).take R.log))
  | [] => hs_pure ⟨fun _ h => absurd h List.not_mem_nil, rfl, rfl⟩
  | R :: rs => by
    simp only [regParts2, mapB]
    refine hs_bind (hs_bind (hs_eqConst2 hz ho hoK _ _) fun s hs => hs_pure (P := fun e : C2 × Placement × List C2 =>
      KC2 e.1 ∧ e.2 = ((⟨R.log, R.off⟩ : Placement), ry.take R.log) ∧
        e.1.val M = hiWG (ry.map (C2.val M)) R.log R.base) ⟨hs.1, rfl, by rw [hs.2, hiWG, List.map_drop]⟩)
      fun e ⟨heK, he, hev⟩ => ?_
    refine hs_bind (hs_regParts2 hz ho hoK ry rs) fun ps ⟨h1, h2, h3⟩ => hs_pure ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact heK
      · exact h1 x hx
    · rw [List.map_cons, List.map_cons, h2, he]
    · rw [partsV, List.map_cons, List.map_cons, ← partsV, h3]
      obtain ⟨e1, e2⟩ := e
      simp only at he hev
      simp only [List.map_cons, hev, he, List.map_take]

theorem fe6_mul_right_comm (a b d : FE6) : FE6.mul (FE6.mul a b) d = FE6.mul (FE6.mul a d) b := by
  simp only [fe6_mul, FE6.mk.injEq]
  constructor <;> ring

/-- Coordinatewise sums in `Quad Ext3` (`sumW6D`'s and `affWD`'s accumulator). -/
def addW (acc w : FE6) : FE6 := ⟨acc.re + w.re, acc.im + w.im⟩

theorem affWD_eq (N : TNatT) (s : Typed.YSrc) (r : List FE2) (h : Bool) (X : List FE) :
    affWD N s r h X = c6 h (((N.toN.regsOf s).map fun g => FE6.mul (FE6.mul (FE6.ofE2 (hiWG r g.log g.base))
      (wordWD (r.take g.log) (X.take g.log))) (FE6.ofE (eqAtF (X.drop g.log) (g.dst >>> g.log)))).foldl addW ⟨0, 0⟩) := by
  unfold affWD c6
  simp only [List.foldl_map]
  rfl

theorem sumW6D_eq (parts : List (FE2 × Placement × List FE2)) (X : List FE) :
    sumW6D parts X = (parts.map fun e => FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove X)))
      (wordWD e.2.2 (X.take e.2.1.variableCount))).foldl addW ⟨0, 0⟩ := by
  unfold sumW6D
  simp only [List.foldl_map]
  rfl

/-- **V_S's region weight is the parts' split weight** (`affWD` on V's regions, `sumW6D` on the circuit's parts with
the regions' selectors `hiWG`). -/
theorem affWD_parts (N : TNatT) (s : Typed.YSrc) (rs : List TReg) (hrs : (N.toN.regsOf s).map nTrip = rs.map tTrip)
    (ry : List FE2) (h : Bool) :
    (fun X => c6 h (sumW6D (rs.map fun R => (hiWG ry R.log R.base, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) X)) =
      affWD N s ry h := by
  funext X
  rw [affWD_eq, sumW6D_eq]
  congr 2
  let F : ℕ × ℕ × ℕ → FE6 := fun t => FE6.mul (FE6.mul (FE6.ofE2 (hiWG ry t.2.1 t.1))
    (wordWD (ry.take t.2.1) (X.take t.2.1))) (FE6.ofE (eqAtF (X.drop t.2.1) (t.2.2 >>> t.2.1)))
  have e1 : ((N.toN.regsOf s).map fun g => FE6.mul (FE6.mul (FE6.ofE2 (hiWG ry g.log g.base))
      (wordWD (ry.take g.log) (X.take g.log))) (FE6.ofE (eqAtF (X.drop g.log) (g.dst >>> g.log)))) =
      ((N.toN.regsOf s).map nTrip).map F := by rw [List.map_map]; rfl
  rw [e1, hrs, List.map_map, List.map_map]
  refine List.map_congr_left fun R _ => ?_
  simp only [Function.comp_apply, F, tTrip, eqAbove_eqAtF]
  exact fe6_mul_right_comm _ _ _

/-- An `E2` half claim's relation, from its parts' static facts and its block claim. -/
theorem frelZ_half {zc : Cell} {b h : Bool} {parts : List (C2 × Placement × List C2)} {v : Cell}
    (hp : ∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
      e.2.1.variableCount ≤ CMain.nu20)
    (hreg : ∀ e ∈ parts, RegP e.2.1) {bc : BlockClaim}
    (hbc : bc = halfB CMain.nu20 h (partsV M parts) (v.val M)) :
    FRelZ M zc b (.half h parts v) (.main, bc, 0) :=
  ⟨⟨rfl, hp, hbc⟩, hreg, rfl⟩

/-- The table claims of the mini-bus are `C_main` claims taken as they are (`typedClaimsC_ok`'s table part). -/
theorem tabClaims_ok {zc z : Cell} {T : TData} {sOff : ℕ} {tab : List (List Cell × List Cell)}
    (hreg : typedRegB T sOff = true) (hl : ∀ x ∈ T.mbS.zip tab, x.2.1.length = min T.mbR x.1.τ) :
    ∀ cc ∈ tabClaims T.mbS tab z, cOkB zc cc = true ∧ cc.com = .main := by
  obtain ⟨-, -, hS⟩ := typedRegB_sound hreg
  intro cc hcc
  unfold tabClaims at hcc
  obtain ⟨x, hx, hcc⟩ := List.mem_flatMap.mp hcc
  obtain ⟨ci, hci, hcc⟩ := List.mem_filterMap.mp hcc
  have hs := hS x.1 (List.of_mem_zip hx).1
  have hcm : ci.1 ∈ x.1.cols := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hci)
  rcases hc : ci.1 with _ | ⟨rec, off⟩
  · rw [hc] at hcc; exact absurd hcc (by simp)
  · rw [hc] at hcc hcm
    obtain ⟨hrec, hreg'⟩ := hs.2.2 _ hcm rec off rfl
    subst hrec
    simp only [Option.some.injEq] at hcc
    subst hcc
    have hlen := hl x hx
    have hne : (⟨x.1.τ, off⟩ : Placement) ≠ ⟨22, 0⟩ := fun e => by
      have := hreg'.2.2.1; rw [show off = 0 from congrArg Placement.index e] at this; simp at this
    refine ⟨?_, rfl⟩
    simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, hne,
      ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true, and_true]
    refine ⟨⟨hs.2.1, ?_⟩, hreg'⟩
    rw [hlen]; exact Nat.min_eq_right hs.1

theorem kc2_ofK_re {x : C2} (hx : KC2 x) : FE.ofK (x.val M).re = x.re.val M := kcell_val hx.1

theorem kc2_ofK_im {x : C2} (hx : KC2 x) : FE.ofK (x.val M).im = x.im.val M := kcell_val hx.2

/-- A region claim's two halves stand for V_S's (`regClaimsND`), on V's regions. -/
theorem regHalves_rel {zc : Cell} {b : Bool} {N : TNatT} {p : Params} (hν : p.nuMain = CMain.nu20) {s : Typed.YSrc}
    {rs : List TReg} (hrs : (N.toN.regsOf s).map nTrip = rs.map tTrip)
    (hR : ∀ R ∈ rs, R.log ≤ 21 ∧ RegP ⟨R.log, R.off⟩) {ry : List C2} (hry : ry.length = 21)
    (hryK : ∀ x ∈ ry, KC2 x) {ps : List (C2 × Placement × List C2)} (hpK : ∀ e ∈ ps, KC2 e.1)
    (hp2 : ps.map (·.2) = rs.map (fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log)))
    (hpv : partsV M ps = rs.map fun R => (hiWG (ry.map (C2.val M)) R.log R.base, (⟨R.log, R.off⟩ : Placement),
      (ry.map (C2.val M)).take R.log)) {v : C2} (hv : KC2 v) :
    List.Forall₂ (FRelZ M zc b) (halves2 ps v) (regClaimsND N p s (ry.map (C2.val M)) (v.val M)) := by
  have key : ∀ x ∈ ps, ∃ R ∈ rs, x.2 = ((⟨R.log, R.off⟩ : Placement), ry.take R.log) := fun x hx => by
    have : x.2 ∈ ps.map (·.2) := List.mem_map_of_mem hx
    rw [hp2] at this
    obtain ⟨R, hR', e⟩ := List.mem_map.mp this
    exact ⟨R, hR', e.symm⟩
  have hp : ∀ e ∈ ps, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
      e.2.1.variableCount ≤ CMain.nu20 := fun e he => by
    obtain ⟨R, hRm, hE⟩ := key e he
    have hl := (hR R hRm).1
    refine ⟨hpK e he, fun x hx => ?_, ?_, ?_⟩
    · rw [hE] at hx; exact hryK x (List.mem_of_mem_take hx)
    · rw [hE]; simp only [List.length_take, hry]; omega
    · rw [hE]; show R.log ≤ CMain.nu20; simp only [CMain.nu20]; omega
  have hreg : ∀ e ∈ ps, RegP e.2.1 := fun e he => by
    obtain ⟨R, hRm, hE⟩ := key e he
    rw [hE]; exact (hR R hRm).2
  have hw : ∀ h : Bool, affWD N s (ry.map (C2.val M)) h = fun x => c6 h (sumW6D (partsV M ps) x) := fun h => by
    rw [hpv, ← affWD_parts N s rs hrs]
  unfold halves2 regClaimsND
  simp only [List.map_cons, List.map_nil]
  refine .cons (frelZ_half hp hreg ?_) (.cons (frelZ_half hp hreg ?_) .nil)
  · rw [hw false, hν]; unfold halfB; congr 1; exact kc2_ofK_re hv
  · rw [hw true, hν]; unfold halfB; congr 1; exact kc2_ofK_im hv

/-- **The typed claims of blob GT stand for V_S's** (10d): `typedClaimsGT`'s claims, against `typedClaimsND` on the
cells' values and the mini-bus's table claims with tail `0`. -/
theorem typed_relT {zc : Cell} {b : Bool} {N : TNatT} {p : Params} {m : M3} {pub : Pub} {T : TData} {sOff : ℕ}
    {t : TypedCT} {z : Cell} (hz : z.val M = 0) {z2 o2 : C2} (hz2 : z2.val M = 0) (hz2K : KC2 z2) (ho2 : o2.val M = 1)
    (ho2K : KC2 o2) (htd : TdOk T N.toN) (hreg : typedRegB T sOff = true) (hν : p.nuMain = CMain.nu20)
    (hrec : p.nuRec = tR) (hsO : (layout0 p).s = sOff) (hry : t.ry.length = 21) (hryK : ∀ x ∈ t.ry, KC2 x)
    (hrr : t.rr.length = tR) (hrrK : ∀ x ∈ t.rr, KC2 x) (hvR : KC2 t.vR) (hrvK : ∀ x ∈ t.rv, KC2 x)
    (hl : ∀ x ∈ T.mbS.zip t.tab, x.2.1.length = min T.mbR x.1.τ) {st : List Lvm.M3.Tab}
    (hst : T.mbS = st.map Lvm.M3.Tab.shape)
    (hX : m.tableClaims pub (t.tab.map fun e => (vs M e.1, vs M e.2)) =
      Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))) :
    Hs c M (typedClaimsGT z z2 o2 T sOff t) (fun cs => List.Forall₂ (FRelZ M zc b) cs
      (typedClaimsND N p (t.ry.map (C2.val M)) (t.rv.map (C2.val M)) (t.rr.map (C2.val M)) (t.vR.val M) ++
        Shape.zeroTails (m.tableClaims pub (t.tab.map fun e => (vs M e.1, vs M e.2))))) := by
  obtain ⟨h19, hR, -⟩ := typedRegB_sound hreg
  have hrv : ∀ i, KC2 (t.rv.getD i z2) := fun i => by
    rw [List.getD_eq_getElem?_getD]
    rcases h : t.rv[i]? with _ | x
    · exact hz2K
    · exact hrvK x (List.mem_of_getElem? h)
  have hgv : ∀ i, (t.rv.map (C2.val M)).getD i 0 = (t.rv.getD i z2).val M := fun i => by
    rw [← hz2, List.getD_map]
  unfold typedClaimsGT
  refine hs_bind (hs_regParts2 hz2 ho2 ho2K t.ry T.sig) fun pS ⟨hS1, hS2, hS3⟩ => ?_
  refine hs_bind (hs_regParts2 hz2 ho2 ho2K t.ry T.com) fun pC ⟨hC1, hC2, hC3⟩ => ?_
  refine hs_bind (hs_regParts2 hz2 ho2 ho2K t.ry T.ks) fun pK ⟨hK1, hK2, hK3⟩ => hs_pure ?_
  -- the relayout's point claim
  have hrel : List.Forall₂ (FRelZ M zc b) (halves2 [(o2, ⟨tR, sOff⟩, t.rr)] t.vR)
      (Lvm.splitZ p.nuMain [(1, ⟨p.nuRec, (layout0 p).s⟩, t.rr.map (C2.val M))] (t.vR.val M)) := by
    have hp : ∀ e ∈ [(o2, (⟨tR, sOff⟩ : Placement), t.rr)], KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧
        e.2.2.length = e.2.1.variableCount ∧ e.2.1.variableCount ≤ CMain.nu20 := fun e he => by
      rcases List.mem_singleton.mp he with rfl
      exact ⟨ho2K, hrrK, hrr, by show tR ≤ CMain.nu20; decide⟩
    have hpr : ∀ e ∈ [(o2, (⟨tR, sOff⟩ : Placement), t.rr)], RegP e.2.1 := fun e he => by
      rcases List.mem_singleton.mp he with rfl
      exact h19
    have hpv : partsV M [(o2, (⟨tR, sOff⟩ : Placement), t.rr)] =
        [(1, (⟨p.nuRec, (layout0 p).s⟩ : Placement), t.rr.map (C2.val M))] := by
      rw [partsV, List.map_singleton, ho2, hrec, hsO]
    unfold halves2 Lvm.splitZ Lvm.splitD
    simp only [List.map_cons, List.map_nil]
    refine .cons (frelZ_half hp hpr ?_) (.cons (frelZ_half hp hpr ?_) .nil)
    · rw [hpv, hν]; unfold halfB; congr 1; exact kc2_ofK_re hvR
    · rw [hpv, hν]; unfold halfB; congr 1; exact kc2_ofK_im hvR
  have hR' : ∀ {rs : List TReg}, (∀ R ∈ rs, R ∈ T.sig ++ T.com ++ T.ks) →
      ∀ R ∈ rs, R.log ≤ 21 ∧ RegP ⟨R.log, R.off⟩ := fun hsub R hRm => hR R (hsub R hRm)
  have hσ := regHalves_rel (zc := zc) (b := b) hν htd.sig (hR' (by intro R h; simp [h])) hry hryK hS1 hS2 hS3 (hrv 2)
  have hcm := regHalves_rel (zc := zc) (b := b) hν htd.com (hR' (by intro R h; simp [h])) hry hryK hC1 hC2 hC3 (hrv 0)
  have hks := regHalves_rel (zc := zc) (b := b) hν htd.ks (hR' (by intro R h; simp [h])) hry hryK hK1 hK2 hK3 (hrv 3)
  rw [← hgv 2] at hσ
  rw [← hgv 0] at hcm
  rw [← hgv 3] at hks
  -- the mini-bus's table claims
  have htab := tabClaims_ok (zc := zc) (z := z) hreg hl
  have hv := tabClaims_val hz st t.tab
  rw [← hst] at hv
  have htr : List.Forall₂ (FRelZ M zc b) ((tabClaims T.mbS t.tab z).map .e3)
      (Shape.zeroTails (m.tableClaims pub (t.tab.map fun e => (vs M e.1, vs M e.2)))) := by
    refine e3s_rel ?_ ?_ (fun cc hcc => (htab cc hcc).1)
    · rw [hX, hv]; simp [Shape.zeroTails, Function.comp_def]
    · intro e he
      rw [hX, ← hv, Shape.zeroTails, List.map_map] at he
      obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he
      exact ⟨(htab cc hcc).2, rfl⟩
  unfold typedClaimsND
  exact List.rel_append (List.rel_append (List.rel_append (List.rel_append hrel hσ) hcm) hks) htr

end Lvm.E2Q
