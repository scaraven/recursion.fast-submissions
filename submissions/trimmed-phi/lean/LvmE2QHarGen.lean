-- New for lvm2 U-TAPE (UT-C3, closure): the generic Q_arith lemmas of S2GF (from `LvmE2QHarF`) and of S2GT (the
-- module `LvmE2QHarT`, now a stub importing this one), so that a stage's harith need not import S2GF's instance
-- (`LvmE2QInst`, `LvmE2QInstT`) or S2GF's front gadgets (`LvmE2QHarFront`).
import LvmE2QHarPos
import LvmE2QTypedReg
import LvmQTypedHarS
import LvmFinPos
import LvmQAsmHarTails
import LvmE2QPin
import LvmE2QOpenPhaseP
import LvmE2QTypedT
import LvmE2QNodeG
import LvmE2TV
import LvmQAsmBorrow
import LvmQRingCrtL
import LvmE2QWPhase
import LvmQWireSound
import LvmE2QKLayer
import LvmE2QOpenPhase
import LvmE2QAsmFront

/-!
# The generic part of Q_arith at S2GF

`cfgMainF`'s fields, `layOkF_pb`, `ok_bindV`, `cclaim_point`, `mapB_len`, `pinG_fst`, the typed claims taken as they
are (`tailFreeB`, `cOkB`, `e3s_rel`, `typedClaimsC_ok`) and the typed gadgets' shapes.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

/-- A builder's trivial invariant. -/
theorem hs_true {c : Ctx} {M : Mem} {α : Type} (m : BM α) : Lvm.Har.Hs c M m (fun _ => True) := fun _ _ => trivial

theorem cfgMainF_U (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).U = phaseLane p .openMain 0 - 5 := rfl

theorem stackEnd_cfgMainF (p : Params) (pb pw : Nat → Nat) :
    Lvm.Har.stackEndL (cfgMainF p pb pw).g (cfgMainF p pb pw).ood (cfgMainF p pb pw).levels ((cfgMainF p pb pw).U + 15) =
      Lvm.Har.stackEndL p.grind p.mainOod p.mainLevels (phaseLane p .openMain 0 - 5 + 15) := rfl

theorem cfgMainF_levels (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).levels = p.mainLevels := rfl
theorem cfgMainF_g (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).g = p.grind := rfl
theorem cfgMainF_pw (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).pw = pw := rfl
theorem cfgMainF_pb (p : Params) (pb pw : Nat → Nat) (i : Nat) : (cfgMainF p pb pw).pb i = pb i := rfl
theorem cfgMainF_ood (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).ood = p.mainOod := rfl

/-- `LayOk` of `C_main`'s opening does not read the position and PoW bases. -/
theorem layOkF_pb (p : Params) (pb pw pb' pw' : Nat → Nat) (T : Nat) :
    Lvm.Har.LayOk (cfgMainF p pb pw) T = Lvm.Har.LayOk (cfgMainF p pb' pw') T :=
  Lvm.Har.layOk_pb _ _ _ pb pb' _ _ _ _ pw pw' T


/-- A bind's output and next pointer as opaque variables (`generalize` would substitute the builder's run back into
the proof term, and the kernel then evaluates it). -/
theorem ok_bindV {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Lvm.QSig.Ok c M (m >>= f) p) :
    ∃ a q, (m p).1 = a ∧ p.e ≤ q.e ∧ Lvm.QSig.Ok c M m p ∧ Lvm.QSig.Ok c M (f a) q := by
  obtain ⟨h1, h2⟩ := Lvm.Har.okb h
  exact ⟨_, _, rfl, Lvm.Har.adv_e_le _ _, h1, h2⟩

theorem cclaim_point (M : Mem) (blk : Placement) (z : List Cell) (a : Cell) :
    Lvm.Har.CClaim.val M ⟨.main, .point blk z, a⟩ = (.main, BlockClaim.point blk (Lvm.Har.vs M z) (a.val M)) := rfl

theorem mapB_len {α β : Type} (f : α → BM β) : ∀ (l : List α) (p : Ptr), (Lvm.Q2.mapB f l p).1.length = l.length
  | [], _ => rfl
  | a :: l, p => by
    simp only [Lvm.Q2.mapB, bind_apply, pure_apply, List.length_cons]
    rw [mapB_len f l]

/-- The pin gadget's claim is a point claim on `⟨ν, 0⟩` (generic: no builder run). -/
theorem pinG_fst (nu qz qa : Nat) (p : Ptr) :
    ∃ z a, (Lvm.Q2.pinG nu qz qa p).1 = ⟨.main, .point ⟨nu, 0⟩ z, a⟩ ∧ z.length = (List.range nu).length :=
  ⟨_, _, rfl, mapB_len _ _ _⟩

/-! ## The typed phases' claims (`htrel`) -/

/-- A claim off `D` and the ring by its form (its tail `0` in both shapes). -/
def tailFreeB (cc : Lvm.Har.CClaim) : Bool :=
  match cc.cw with
  | .point blk _ => blk != ⟨22, 0⟩
  | .ring blk _ _ => blk != ⟨CMain.nu20, 0⟩
  | .sum _ _ => true

/-- **A claim the opening takes as it is**: well formed at `ν = 23`, regular in the small shape, tail-free. -/
def cOkB (zc : Cell) (cc : Lvm.Har.CClaim) : Bool :=
  Lvm.Har.WF1 CMain.nu20 cc && Lvm.QShape.ZWF zc cc && tailFreeB cc

theorem tailC_free {M : Mem} {cc : Lvm.Har.CClaim} (h : tailFreeB cc = true) : Lvm.QShape.tailC M cc = 0 := by
  unfold tailFreeB at h
  unfold Lvm.QShape.tailC
  rcases hcw : cc.cw with ⟨blk, zl⟩ | ⟨blk, pt, cs⟩ | ⟨nu, parts⟩ <;> rw [hcw] at h <;> simp_all

/-- **Claims of `C_main` taken as they are** stand for V's claims with tail `0` (`FRelZ`, both shapes). -/
theorem e3s_rel {M : Mem} {zc : Cell} {b : Bool} : ∀ {cs : List Lvm.Har.CClaim} {cls : List (Com × BlockClaim × FE)},
    cs.map (Lvm.Har.CClaim.val M) = cls.map (fun e => (e.1, e.2.1)) → (∀ e ∈ cls, e.1 = .main ∧ e.2.2 = 0) →
    (∀ cc ∈ cs, cOkB zc cc = true) → List.Forall₂ (Lvm.Q2.FRelZ M zc b) (cs.map .e3) cls
  | [], [], _, _, _ => .nil
  | cc :: cs, e :: cls, h, he, hc => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hc0 := hc cc (List.mem_cons_self ..)
    simp only [cOkB, Bool.and_eq_true] at hc0
    obtain ⟨⟨hw, hz⟩, ht⟩ := hc0
    obtain ⟨hm, h0⟩ := he e (List.mem_cons_self ..)
    exact .cons ⟨⟨hm, hw, (congrArg Prod.snd h.1).symm⟩, hz, fun _ => by rw [h0, tailC_free ht]⟩
      (e3s_rel h.2 (fun e' he' => he e' (List.mem_cons_of_mem _ he'))
        (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')))
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

theorem hs_bind_true {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {Q : β → Prop}
    (h : ∀ a, Lvm.Har.Hs c M (f a) Q) : Lvm.Har.Hs c M (m >>= f) Q :=
  Lvm.Har.hs_bind (hs_true m) fun a _ => h a

theorem hs_seqAll_snd {c : Ctx} {M : Mem} {α β γ : Type} {f : α → BM (β × γ)} (g : α → γ)
    (hf : ∀ a, Lvm.Har.Hs c M (f a) (fun x => x.2 = g a)) :
    ∀ l : List α, Lvm.Har.Hs c M (seqAll (l.map f)) (fun ps => ps.map (·.2) = l.map g)
  | [] => Lvm.Har.hs_pure rfl
  | a :: l => Lvm.Har.hs_bind (hf a) fun x hx => Lvm.Har.hs_bind (hs_seqAll_snd g hf l) fun xs hxs =>
      Lvm.Har.hs_pure (by rw [List.map_cons, List.map_cons, hx, hxs])

/-- A region claim's form: a sum over the regions' blocks at `r_y`'s low coordinates. -/
theorem regClaimG_shape {c : Ctx} {M : Mem} (z o : Cell) (com : Com) (nu : ℕ) (rs : List Lvm.QTyped.TReg)
    (ry : List Cell) (v : Cell) :
    Lvm.Har.Hs c M (Lvm.QTyped.regClaimG z o com nu rs ry v) (fun cc => ∃ parts : List (Cell × Placement × List Cell),
      cc = ⟨com, .sum nu parts, v⟩ ∧
        parts.map (·.2) = rs.map fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log)) := by
  unfold Lvm.QTyped.regClaimG
  refine Lvm.Har.hs_bind (hs_seqAll_snd (fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log))
    (fun R => hs_bind_true fun _ => Lvm.Har.hs_pure rfl) rs) fun parts hp => Lvm.Har.hs_pure ⟨parts, rfl, hp⟩

theorem regClaim_ok {zc : Cell} {com : Com} {rs : List Lvm.QTyped.TReg} {ry : List Cell} {v : Cell}
    {parts : List (Cell × Placement × List Cell)} (hry : ry.length = 21)
    (hrs : ∀ R ∈ rs, R.log ≤ 21 ∧ Lvm.QShape.RegP ⟨R.log, R.off⟩)
    (hp : parts.map (·.2) = rs.map fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log)) :
    cOkB zc ⟨com, .sum CMain.nu20 parts, v⟩ = true := by
  have key : ∀ x ∈ parts, ∃ R ∈ rs, x.2 = ((⟨R.log, R.off⟩ : Placement), ry.take R.log) := fun x hx => by
    have : x.2 ∈ parts.map (·.2) := List.mem_map_of_mem hx
    rw [hp] at this
    obtain ⟨R, hR, e⟩ := List.mem_map.mp this
    exact ⟨R, hR, e.symm⟩
  simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    and_true]
  refine ⟨⟨le_refl _, fun x hx => ?_⟩, trivial, fun x hx => ?_⟩
  · obtain ⟨R, hR, e⟩ := key x hx
    rw [e]
    have := (hrs R hR).1
    simp only [List.length_take, hry]
    exact ⟨by show R.log ≤ CMain.nu20; simp only [CMain.nu20]; (clear * - R ry this; omega), by show min R.log 21 = R.log; (clear * - R ry this; omega)⟩
  · obtain ⟨R, hR, e⟩ := key x hx
    rw [e]; exact (hrs R hR).2

theorem zip_map_take {α β γ : Type} (pts : List γ) (τ : α → ℕ) : ∀ (S : List α) (E : List β),
    ∀ x ∈ S.zip ((S.zip E).map fun y => (pts.take (τ y.1), y.2)), x.2.1.length = min pts.length (τ x.1)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: S, e :: E => by
    intro x hx
    simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [Nat.min_comm]
    · exact zip_map_take pts τ S E x hx

/-- The mini-bus's table points have `min R τ` coordinates. -/
theorem tabG_pts {c : Ctx} {M : Mem} (S : List Lvm.Har.TShape) (R P : ℕ) (z o g : Cell) (bc : Lvm.Har.BusC) :
    Lvm.Har.Hs c M (Lvm.Har.tabG S R P z o g bc) (fun out => ∀ x ∈ S.zip out, x.2.1.length = min R x.1.τ) := by
  unfold Lvm.Har.tabG
  iterate 20 refine hs_bind_true fun _ => ?_
  refine Lvm.Har.hs_bind (hs_true _) fun r _ => ?_
  iterate 4 refine hs_bind_true fun _ => ?_
  refine Lvm.Har.hs_pure fun x hx => ?_
  have := zip_map_take (((List.range R).map (Lvm.Har.chC r.2)).reverse) (·.τ) S _ x hx
  simpa using this

theorem wireGX_ry {c : Ctx} {M : Mem} (z o g : Cell) (T : Lvm.QTyped.TData) (pb P n : ℕ) (v : List Cell) :
    Lvm.Har.Hs c M (wireGX z o g T pb P n v) (fun w => w.1.length = 21) := by
  unfold wireGX
  iterate 17 refine hs_bind_true fun _ => ?_
  exact Lvm.Har.hs_pure (by simp)

theorem relayG_rr {c : Ctx} {M : Mem} (z o g : Cell) (T : Lvm.QTyped.TData) (P : ℕ) (ry : List Cell) (vS : Cell) :
    Lvm.Har.Hs c M (Lvm.QTyped.relayG z o g T P ry vS) (fun r => r.1.length = 19) := by
  unfold Lvm.QTyped.relayG
  iterate 6 refine hs_bind_true fun _ => ?_
  exact Lvm.Har.hs_pure (by simp)

/-- **The typed gadget's points**: `r_y` (21), `r''` (19), the tables' (`min mbR τ`). -/
theorem typedGX_shape {c : Ctx} {M : Mem} (T : Lvm.QTyped.TData) (pb P accV : ℕ) (z o : Cell) :
    Lvm.Har.Hs c M (typedGX T pb P accV z o) (fun t => t.ry.length = 21 ∧ t.rr.length = 19 ∧
      ∀ x ∈ T.mbS.zip t.tab, x.2.1.length = min T.mbR x.1.τ) := by
  unfold typedGX
  refine hs_bind_true fun zr => Lvm.Har.hs_bind (wireGX_ry _ _ _ _ _ _ _ _) fun w hw => ?_
  refine Lvm.Har.hs_bind (relayG_rr _ _ _ _ _ _ _) fun r hr => hs_bind_true fun _ => ?_
  unfold Lvm.QTyped.miniG
  refine Lvm.Har.hs_bind (Lvm.Har.hs_bind (hs_true _) fun bus _ => Lvm.Har.hs_bind (tabG_pts _ _ _ _ _ _ _)
    fun tab ht => hs_bind_true fun _ => Lvm.Har.hs_pure (show ∀ x ∈ T.mbS.zip (bus, tab).2, _ from ht))
    fun mb hmb => Lvm.Har.hs_pure ⟨hw, hr, hmb⟩

/-- **The typed claims are taken as they are**: two in the first list (no `C_rec` table claim), every claim
`cOkB`. -/
theorem typedClaimsC_ok {c : Ctx} {M : Mem} {z o zc : Cell} {T : Lvm.QTyped.TData} {sOff : ℕ}
    {t : Lvm.QTyped.TypedC} {nu : ℕ} (hnu : nu = CMain.nu20) (hreg : typedRegB T sOff = true)
    (hry : t.ry.length = 21) (hrr : t.rr.length = 19) (hl : ∀ x ∈ T.mbS.zip t.tab, x.2.1.length = min T.mbR x.1.τ) :
    Lvm.Har.Hs c M (Lvm.QTyped.typedClaimsC z o T nu sOff t)
      (fun tc => tc.1.length = 2 ∧ ∀ cc ∈ tc.1 ++ tc.2, cOkB zc cc = true) := by
  subst hnu
  obtain ⟨h19, hR, hS⟩ := typedRegB_sound hreg
  have htab : ∀ cc ∈ Lvm.Har.tabClaims T.mbS t.tab z, cOkB zc cc = true ∧ cc.com = .main := by
    intro cc hcc
    unfold Lvm.Har.tabClaims at hcc
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
  unfold Lvm.QTyped.typedClaimsC
  refine Lvm.Har.hs_bind (regClaimG_shape _ _ _ _ _ _ _) fun cS ⟨pS, eS, hpS⟩ => ?_
  refine Lvm.Har.hs_bind (regClaimG_shape _ _ _ _ _ _ _) fun cC ⟨pC, eC, hpC⟩ => ?_
  refine Lvm.Har.hs_bind (regClaimG_shape _ _ _ _ _ _ _) fun cK ⟨pK, eK, hpK⟩ => Lvm.Har.hs_pure ?_
  have hnil : (Lvm.Har.tabClaims T.mbS t.tab z).filter (·.com == .crec) = [] :=
    List.filter_eq_nil_iff.mpr fun cc hcc => by simp [(htab cc hcc).2]
  refine ⟨by simp [hnil], fun cc hcc => ?_⟩
  rw [hnil] at hcc
  have h19' : (⟨Lvm.QTyped.tR, sOff⟩ : Placement) ≠ ⟨22, 0⟩ := by simp
  rcases List.mem_append.mp hcc with h | h
  · rcases List.mem_cons.mp h with rfl | h
    · simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, hrr, h19',
        ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true, and_true]
      exact ⟨by decide, h19⟩
    · rcases List.mem_cons.mp h with rfl | h
      · rw [eS]; exact regClaim_ok hry (fun R hR' => hR R (by simp [hR'])) hpS
      · simp at h
  · rcases List.mem_cons.mp h with rfl | h
    · rw [eC]; exact regClaim_ok hry (fun R hR' => hR R (by simp [hR'])) hpC
    · rcases List.mem_cons.mp h with rfl | h
      · rw [eK]; exact regClaim_ok hry (fun R hR' => hR R (by simp [hR'])) hpK
      · exact (htab cc (List.mem_filter.mp h).1).1


/-! ## Generic facts of S2GF's harith modules (from `LvmE2QHarFacts`, `LvmE2QHarIn`, `LvmE2QHarPosOk`) -/

section HarFacts

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS Lvm.Typed
open Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-! ## The ground answers' proof of work -/

/-- An answer of the list has its recomposition row among `powRecRows`, its bit words inside the region. -/
theorem powRecRows_mem : ∀ (bw : ℕ) (as : List (ℕ × ℕ)) {q g : ℕ}, (q, g) ∈ as →
    ∃ bw', bw ≤ bw' ∧ bw' + (64 - g) ≤ bw + Lvm.Q2.powWords as ∧ powRecRow g bw' q ∈ powRecRows bw as
  | _, [], _, _, h => absurd h List.not_mem_nil
  | bw, (q', g') :: as, q, g, h => by
    have hw : Lvm.Q2.powWords ((q', g') :: as) = (64 - g') + Lvm.Q2.powWords as := by
      simp only [Lvm.Q2.powWords, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨bw, le_rfl, by rw [hw]; (clear * - bw g as q; omega), List.mem_cons_self⟩
    · obtain ⟨b, h1, h2, hb⟩ := powRecRows_mem (bw + (64 - g')) as h
      exact ⟨b, by (clear * - bw b q' g' as g h1; omega), by rw [hw]; (clear * - b g bw g' as q' h2; omega), List.mem_cons_of_mem _ hb⟩

/-- `n mod 2^(k+1)` is `n mod 2^k` plus bit `k`'s weight. -/
theorem mod_two_pow_succ' (n k : ℕ) : n % 2 ^ (k + 1) = n % 2 ^ k + (if n.testBit k then 2 ^ k else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

/-- **The booleanity runs cover the region**: every offset `o` with `n − n mod 2^k ≤ o < n` lies in the run of one set
bit `a < k`. -/
theorem boolRuns_cover (bw n : ℕ) : ∀ (k o : ℕ), n - n % 2 ^ k ≤ o → o < n →
    ∃ a b, (⟨a, [Lvm.Q2.rowBoolL b]⟩ : ABlk) ∈ boolRuns bw n k ∧ b ≤ bw + o ∧ bw + o < b + 2 ^ a
  | 0, o, h1, h2 => by rw [pow_zero, Nat.mod_one, Nat.sub_zero] at h1; omega
  | k + 1, o, h1, h2 => by
    have hm := mod_two_pow_succ' n k
    have hle : n % 2 ^ k ≤ n := Nat.mod_le _ _
    have hle' : n % 2 ^ (k + 1) ≤ n := Nat.mod_le _ _
    by_cases ho : n - n % 2 ^ k ≤ o
    · obtain ⟨a, b, hb, h3, h4⟩ := boolRuns_cover bw n k o ho h2
      exact ⟨a, b, by rw [boolRuns]; exact List.mem_append_right _ hb, h3, h4⟩
    · have ht : n.testBit k = true := by
        by_contra hf
        rw [Bool.not_eq_true] at hf
        rw [hf, if_neg (by simp), Nat.add_zero] at hm
        (clear * - n k o h1 hm hle ho; omega)
      rw [ht, if_pos rfl] at hm
      refine ⟨k, bw + (n - n % 2 ^ (k + 1)), ?_, by (clear * - bw n k o h1; omega), by (clear * - bw o n k hm hle hle' ho; omega)⟩
      rw [boolRuns, ht, if_pos rfl]
      exact List.mem_append_left _ List.mem_cons_self

/-- A row of the layout's auxiliary blocks holds at each of its block's iterations. -/
theorem auxRow_mem {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} (hlay : tl.Ok Q) (hone : z tl.one = 1)
    (h : WiringRelX Q tl z) {B : ABlk} (hB : B ∈ tl.aux) {r : ARow} (hr : r ∈ B.rows) {j : ℕ} (hj : j < 2 ^ B.l) :
    ARowHolds tl z j r := by
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.mp hB
  have hget : tl.aux.getD k default = B := by rw [List.getD_eq_getElem _ _ hk, hkb]
  obtain ⟨r', hr', hrr⟩ := List.mem_iff_getElem.mp hr
  have hj' : j < 2 ^ (tl.aux.getD k default).l := by rw [hget]; exact hj
  have hr'' : r' < (tl.aux.getD k default).rows.length := by rw [hget]; exact hr'
  have := auxRow_of_wiringX Q tl z hlay hone h hk hj' hr''
  rw [hget, List.getD_eq_getElem _ _ hr', hrr] at this
  exact this

/-- **V's proof-of-work checks from the PoW blocks** (`powBlk_ok`): on the layout built with `specQF C Q pw`, where
the coordinate-split relation holds and the word `1` holds `1`, every answer `(q, g)` of `pw` (with `g ≤ 64` and its
lane 2 streamed) passes `powOKR g` on `Σ`'s scalar at lane `q`; hence `PowOkV (feAt Σ) L` for every `L ⊆ pw`. -/
theorem powOk_of_blks (C : QCfg) {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} {pw : List (ℕ × ℕ)}
    {d : Array (Ty × ℕ × ℕ)} (hl : tl = (mkLayD Q (Lvm.E2Q.specQF C Q pw) d).1) (hlay : tl.Ok Q)
    (hone : z tl.one = 1) (h : WiringRelX Q tl z) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memOf tl z) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ pw)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L := by
  intro a ha
  obtain ⟨q, g⟩ := a
  have hapw := hL _ ha
  obtain ⟨hq, hg⟩ := hpw _ ha
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQF C Q pw) d
  have haux : tl.aux = (specQ C Q).auxOf f ++ (Lvm.Q2.rowAuxL (f (specQ C Q).auxWords.length) (tBw C) (wireSlices C.p) ++
      Lvm.Q2.rowAuxL (f ((specQ C Q).auxWords.length + 1)) (tBk C) (ksSlices C.p)) ++
      powBlksL (f ((specQ C Q).auxWords.length + 2)) pw := by rw [hl, hf]; rfl
  set bw := f ((specQ C Q).auxWords.length + 2) with hbw
  have hP : ∀ B ∈ powBlksL bw pw, B ∈ tl.aux := fun B hB => by rw [haux]; exact List.mem_append_right _ hB
  obtain ⟨bw', h1, h2, hb⟩ := powRecRows_mem bw pw hapw
  have hrows : ∀ r ∈ (Lvm.Q2.powBlk g bw' q).rows, ARowHolds tl z 0 r := by
    intro r hr
    rw [Lvm.Q2.powBlk, powRangeRows] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_range] at hi
      -- booleanity of the word `bw' + i`: its run in `boolRuns`
      obtain ⟨a, b, hB, hb1, hb2⟩ := boolRuns_cover bw (Lvm.Q2.powWords pw) ((Lvm.Q2.powWords pw).log2 + 1) (bw' + i - bw)
        (by rw [Nat.mod_eq_of_lt Nat.lt_log2_self]; (clear * - pw bw' i bw C Q T q g f h1; omega)) (by (clear * - bw' i bw pw C Q T q g f h1 h2 hi; omega))
      have hBm : (⟨a, [Lvm.Q2.rowBoolL b]⟩ : ABlk) ∈ tl.aux := hP _ (List.mem_append_left _ hB)
      have hj : bw' + i - b < 2 ^ a := by (clear * - bw' i b a C Q pw T q g f hb1 hb2; omega)
      refine (Lvm.Q2.aRowHolds_congr ?_).mpr (auxRow_mem hlay hone h hBm List.mem_cons_self hj)
      simp only [Lvm.Q2.aRowVals, Lvm.Q2.rowBoolL, List.map_cons, List.map_nil, aopVal, Nat.mul_zero, Nat.add_zero,
        Nat.one_mul, show b + (bw' + i - b) = bw' + i by (clear * - b bw' i C Q pw T q g f h1 a hb1; omega)]
    · rw [List.mem_singleton] at hr
      subst hr
      exact auxRow_mem hlay hone h (hP _ (List.mem_append_right _ List.mem_cons_self)) hb (by simp)
  have hc : (memOf tl z).k (q + 2) = (feAt sig (8 * q)).c₂ := by
    rw [hS _ hq]
    show kAt sig (8 * (q + 2)) = kAt sig (8 * q + 16)
    rw [show 8 * (q + 2) = 8 * q + 16 by ring]
  exact Lvm.Q2.powBlk_ok tl z hg hc hrows


end HarFacts

section HarIn

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS Lvm.Typed
open Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-- **The bits of `s'`** from the `s'` bit class `sSpec` (`sBits_on`, any configuration). -/
theorem sBits_onC {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v) : Lvm.Q1.SBitsS v (sigIn C).hd (bsB C) := by
  intro l hl z hz
  have hS : sSpec C (bplOf noData (6 + nPosCls C)) ∈ bspecs C noData :=
    List.mem_append_right _ (by simp)
  have hlen : (sSpec C (bplOf noData (6 + nPosCls C))).outs.length = 64 := by
    show ((List.range 64).map BOut.bit).length = 64; simp
  have hout : (sSpec C (bplOf noData (6 + nPosCls C))).out z = .bit z := by
    show ((List.range 64).map BOut.bit).getD z (.bit 0) = .bit z
    rw [List.getD_eq_getElem _ _ (by simpa using hz)]
    simp
  exact out1_ofC hv hS rfl (y := l) (j := z) hl (by rw [hlen]; exact hz) rfl rfl hout (show z < 64 from hz)

/-- **The PoW fields** (`pw_on`, any configuration): the class `powSpec` writes the low `64 − g` bits of each
opening's PoW lane. -/
theorem pw_onC {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v) (hg : 1 ≤ 64 - C.p.grind) :
    ∀ k < (opens C.p).length, (v (pwB C + k)).val.toNat < 2 ^ (64 - C.p.grind) := by
  intro k hk
  have hS : powSpec C (bplOf noData (7 + nPosCls C)) ∈ bspecs C noData :=
    List.mem_append_right _ (by simp)
  have eout : (powSpec C (bplOf noData (7 + nPosCls C))).out 0 = .fld 0 (64 - C.p.grind) 0 := by
    simp only [powSpec, BitsTab.BSpec.out, List.getD_cons_zero]
  have hx : k < (powSpec C (bplOf noData (7 + nPosCls C))).n := by
    simp only [powSpec]; exact hk
  have h1 := out1_ofC hv hS rfl hx (j := 0) (Bc := pwB C + k) (by simp [powSpec]) rfl rfl eout
    ⟨by decide, hg, by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - C; omega))⟩
  unfold Out1 at h1
  rw [h1]
  show ((BOut.fld 0 (64 - C.p.grind) 0).word _).toNat < _
  exact fld_lt' _ hg (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - C; omega)))

/-- **A row switch's words from its looped blocks** (`rowAuxL_sound`): when the three `rowAuxL` blocks are blocks of
the layout and the wiring relation holds, the free cells `t_j` are V's row words of the slices. -/
theorem rowWords_of_aux {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} (hlay : tl.Ok Q) (hone : z tl.one = 1)
    (h : WiringRelX Q tl z) {bw tB qs : ℕ} (hmem : ∀ B ∈ Lvm.Q2.rowAuxL bw tB qs, B ∈ tl.aux) {j : ℕ}
    (hj : j < 128) : (memOf tl z).k (tB + j) = rowWordD (Lvm.Q2.slicesOf (memOf tl z) qs) j := by
  refine Lvm.Q2.rowAuxL_sound (bw := bw) (tB := tB) (qs := qs) tl z (fun B hB i hi r hr => ?_) hj
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.mp (hmem B hB)
  obtain ⟨r', hr', hrr⟩ := List.mem_iff_getElem.mp hr
  have hget : tl.aux.getD k default = B := by rw [List.getD_eq_getElem _ _ hk, hkb]
  have := auxRow_of_wiringX Q tl z hlay hone h hk (by rw [hget]; exact hi) (by rw [hget]; exact hr')
  rw [hget, List.getD_eq_getElem _ _ hr', hrr] at this
  exact this


/-- **The bits of `s'` as `sBitsD`** on the `s'` bit cells. -/
theorem sBitsD_of {v : ℕ → FK} {hd sb : ℕ} (h : Lvm.Q1.SBitsS v hd sb) {s : List FK}
    (hs : s = (List.range 4).map fun l => v (hd + 9 + l)) :
    ∀ i < 256, v (sb + i) = if sBitsD s i then 1 else 0 := by
  intro i hi
  have h1 := h (i / 64) (by (clear * - i hi; omega)) (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [show sb + 64 * (i / 64) + i % 64 = sb + i by (clear * - sb i; omega)] at h1
  unfold Lvm.QSig.Out1 at h1
  rw [h1, Lvm.Q1.bitWord _ (Nat.mod_lt _ (by norm_num)), hs]
  simp only [sBitsD, decide_eq_true hi, Bool.true_and, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show i / 64 < 4 by (clear * - i hi; omega)), Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- **The child's `n'`, its bits and range, the bits of `s'`** (the front's inputs from Q_sig's `SigBits`, its
`ChildOk` and the `s'` bit class), on any memory whose stream is `Σ`. -/
theorem frontIns {C : QCfg} {M : Mem} {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) (hT : 29 ≤ T)
    {o : SigOut} (hbits : SigBits (sigIn C) o M.k) (hch : ChildOk (sigIn C) M.k)
    (hsb : Lvm.Q1.SBitsS M.k (sigIn C).hd (bsB C)) (accV : ℕ) (vk cL : Vector UInt8 32)
    (hln : (sigIn C).ln = 20) (hhd : (sigIn C).hd + 13 = nLane) :
    (∀ j < 20, (kc ((sigIn C).bn + 2 + j)).val M = bitE (pubOfA accV vk cL sig).n j) ∧
      (1 ≤ (pubOfA accV vk cL sig).n ∧ (pubOfA accV vk cL sig).n ≤ 2 ^ 20) ∧
      ∀ i < 256, M.k (bsB C + i) = if sBitsD (pubOfA accV vk cL sig).s i then 1 else 0 := by
  have hn : (pubOfA accV vk cL sig).n = (M.k nLane).val.toNat := pub_n hS hT vk cL
  refine ⟨fun j hj => ?_, ?_, sBitsD_of hsb ?_⟩
  · rw [hn, Cell.val_K]
    exact bitE_out1 (by (clear * - j C M sig T accV vk cL hj; omega)) (hhd ▸ hbits.n_bit j (show j ≤ (sigIn C).ln by (clear * - j C M sig T accV vk cL hln hj; omega)))
  · rw [hn, ← hhd, ← hln]
    exact ⟨hch.2.2.1, hch.2.2.2.1⟩
  · rw [show (pubOfA accV vk cL sig).s = (pubOf vk cL sig).s from rfl, pub_s hS hT vk cL]
    refine List.map_congr_left fun l _ => ?_
    rw [sLane_eq]
    rfl


end HarIn

section HarPosOk

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS Lvm.Typed
open Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

section OnC

variable {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v)
include hv

/-- An output of a position class's row, in `Out1` form (`out1_entryT` for any configuration). -/
theorem out1_entryC {k l x : ℕ} {o : OpenInfo} (hk : k < (opens C.p).length)
    (ho : (opens C.p).getD k default = o) (hl : l < QAsm.nLanes o.L.height) (hx : x < nRows o)
    {e : BOut × ℕ × ℕ} (he : e ∈ laneOuts o.L.height l) (hve : e.1.Valid) :
    Out1 v (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e) := by
  subst ho
  obtain ⟨S, hS, -, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ :=
    posSpecs_hit C (fun c ↦ bplOf noData (6 + c)) hk hl hx he
  exact out1_ofC hv (posSpecs_memC C hS) hrd hy hjo hwc hoc hout hve

/-- `posVal_on` from the position classes' outputs (`posVal_onT` for any configuration). -/
theorem posVal_onC (hS : StreamOk C.p) (hQ : QOk C.p (lay C)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, v ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    v ((lay C).fl + posIdx C.p k j) + v ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8)
        (j % 8 * ((opens C.p).getD k default).L.height) ((opens C.p).getD k default).L.height) :=
  posVal_on C (out1_entryC hv) hS hQ hs hk hH hj

end OnC

/-- **`PosOk` from the position cells' values** (`Lvm.Fin.posOk_of` for any parameter set `p = Cq.p`). -/
theorem posOk_ofG (p : Params) (Cq : QCfg) (hp : Cq.p = p) (C : SCfg) (k0 : ℕ)
    (hpb : ∀ i, C.pb i = posBase Cq (k0 + i)) {Ls : List Level} {V : ℕ}
    (hPL : Lvm.Fin.PosLanes p C.g C.ood Ls V k0) {M : Mem} {ws : List Word} (hS : StreamOk p) (hL : LaneLink p ws)
    (hQ : QOk p (lay Cq))
    (hcell : ∀ k < (opens p).length, ((opens p).getD k default).L.height ≤ 64 →
      ∀ j < ((opens p).getD k default).L.t, M.k (nK Cq + posIdx p k j) =
        kOf (posL p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height)
          ((opens p).getD k default).L.height)) :
    PosOk C M (traceBytesB (decode p ws)) 0 Ls V := by
  intro i hi j hj
  obtain ⟨hk, hLeq, hH, hP⟩ := hPL i hi
  rw [traceBytesB_decode hS hL, hpb, Nat.zero_add]
  have hjt : j < ((opens p).getD (k0 + i) default).L.t := by rw [hLeq]; exact hj
  have ho : (opens p).getD (k0 + i) default ∈ opens p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hjt
  have hin := lanes_in hS h1 hlt
  have hab := ansLane_bound hS hL.size hlt
  have e1 : posBase Cq (k0 + i) + j = nK Cq + posIdx p (k0 + i) j := by
    simp only [posBase, posIdx, hp]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  rw [e1, hcell _ hk (by rw [hLeq]; exact hH) j hjt]
  have hx : j / 8 < nAns ((opens p).getD (k0 + i) default) := by unfold nAns; (clear * - hjt e1; omega)
  have hb : j % 8 * (Ls.getD i default).height + (Ls.getD i default).height ≤ 192 := by rw [← hLeq]; exact h192
  have hlen : 8 * ansLane p (((opens p).getD (k0 + i) default).pe + j / 8) + 24 ≤ hashedLen p := by
    simp only [ansLane, if_neg (show ((opens p).getD (k0 + i) default).pe + j / 8 ≠ 0 by (clear * - h1; omega))]
    (clear * - hin; omega)
  rw [Lvm.Har.qsAt_posL p ws _ _ _ j hj (hP _ hx) hb hlen (by (clear * - hab; omega)), hLeq]
  rfl


end HarPosOk


/-! ## Q_arith at S2GT (from `LvmE2QHarT`) -/

section HarT
/-

# Q_arith at S2GT: the mini-bus record and the typed claims

* **`miniC`** (10e): on a guarded configuration (`NodeGC`), the mini-bus's tables are sumcheck tables and the
  circuit's static data (`tdataOf`) has the record's table shapes, rounds, depth and fixed list (`miniF20` generic in
  the configuration; at S2GT `miniG20`, in `LvmS2GTStmtC`).
* `hs_eqConst2`, `hs_regParts2`: a region's selector at `E2` is `hiWG`; the region parts by value.
* `affWD_parts`: V_S's region weight (`affWD`) is coordinate `h` of the parts' `sumW6D` on V's regions.
* **`typed_relT`** (10d): `typedClaimsGT`'s claims stand for `typedClaimsND ++ zeroTails (table claims)` under
  `FRelZ`, claim for claim (each `E2` claim's halves re then im; the table claims at `E3`, tail `0`).
-/



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
    · rw [hE]; simp only [List.length_take, hry]; (clear * - R p ry hl; omega)
    · rw [hE]; show R.log ≤ CMain.nu20; simp only [CMain.nu20]; (clear * - R p ry hl; omega)
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


end HarT

/-! ## The front's generic gadget facts (from `LvmE2QHarFront`) -/

section FrontGen

open Lvm.Loop.QRing Lvm.Har

variable {c : Ctx} {M : Mem}

theorem borrowGoK_vs (N nb : Nat) : ∀ (k j : Nat) (cy : Cell) (p : Ptr), cy.ty = .K →
    cy.val M = carryE N j → (∀ i < k, (kc (nb + j + i)).val M = bitE N (j + i)) → 1 ≤ N →
    SegsHold c M p (borrowGo nb j k cy p).2 →
    vs M (borrowGo nb j k cy p).1 = (List.range k).map fun i => bitE (N - 1) (j + i)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | k + 1, j, cy, p, hty, hcy, hb, hN, h => by
    simp only [borrowGo] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h2, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h3, -⟩ := h
    have e1 := add_val h1
    have e2 := mad_val h2
    have hb0 := hb 0 (by (clear * - k N; omega))
    simp only [Nat.add_zero] at hb0
    have ih := borrowGoK_vs N nb k (j + 1) _ _ (by rw [mad_out, hty]; rfl)
      (by rw [e2, hcy, hb0, carry_succ]) (fun i hi => by
        rw [show nb + (j + 1) + i = nb + j + (i + 1) by (clear * - nb j i N k; omega), hb (i + 1) (by (clear * - i k N hi; omega))]
        congr 1; (clear * - j i N k; omega)) hN h3
    rw [bind_apply, bind_apply, bind_apply, pure_apply]
    simp only [vs, List.map_cons] at ih ⊢
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map, e1, hb0, hcy, ← pred_bit N j hN,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1; (clear * - j i N; omega)

/-- **`borrowK`'s cells are the bits of `N − 1`** (`o` the `K` one). -/
theorem borrowK_vs {N nb o n : Nat} {p : Ptr} (ho : M.k o = 1) (hb : ∀ j < n, (kc (nb + j)).val M = bitE N j)
    (hN : 1 ≤ N) (h : SegsHold c M p (borrowK nb o n p).2) :
    vs M (borrowK nb o n p).1 = (List.range n).map (bitE (N - 1)) := by
  match n, hb, h with
  | 0, _, _ => rfl
  | k + 1, hb, h =>
    simp only [borrowK] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h2, -⟩ := h
    have e1 := add_val h1
    have hb0 := hb 0 (by (clear * - k N; omega))
    simp only [Nat.add_zero] at hb0
    have hc1 : (add (kc nb) (kc o) p).1.val M = carryE N 1 := by
      rw [e1, hb0, Cell.val_K, ho, ofK_one]
      have := carry_succ N 0
      simp only [carryE, pow_zero, Nat.mod_one, if_true, one_mul, Nat.zero_add] at this ⊢
      rw [this, add_comm]
    have ih := borrowGoK_vs N nb k 1 _ _ rfl hc1 (fun i hi => by
      rw [show nb + 1 + i = nb + (1 + i) by (clear * - nb i N k; omega)]; exact hb (1 + i) (by (clear * - i k N hi; omega))) hN h2
    rw [bind_apply, bind_apply, pure_apply]
    simp only [vs, List.map_cons] at ih ⊢
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map, e1, hb0, Cell.val_K, ho, ofK_one,
      pred_bit N 0 hN]
    simp only [carryE, pow_zero, Nat.mod_one, if_true]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1; (clear * - i N; omega)

/-- `bitsF z m` is the list of `z`'s low `m` bits. -/
theorem bitsF_eq {F : Type} [Field F] : ∀ (m z : Nat),
    (E2V.bitsF z m : List F) = (List.range m).map fun j => if z.testBit j then 1 else 0
  | 0, _ => rfl
  | m + 1, z => by
    rw [E2V.bitsF, bitsF_eq m (z / 2), List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · rw [Nat.testBit_zero]
      by_cases h : z % 2 = 1 <;> simp [h]
    · refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, Nat.testBit_succ]

/-- An `FE` bit's constant coordinate. -/
theorem bitE_c0 (N j : Nat) : (⟨(bitE N j).c₀, (0 : FE).c₀⟩ : FE2) = if N.testBit j then 1 else 0 := by
  unfold bitE
  split <;> rfl

/-- **`K` bit cells paired with a `K` zero** are the bits of `N` in `E2` (`wire_phase`'s `hmb`). -/
theorem kC2_bits {mb : List Cell} {zk : Cell} (hzk : zk.val M = 0) {N m : Nat}
    (h : vs M mb = (List.range m).map (bitE N)) :
    (mb.map fun b => Lvm.Q2.kC2 b zk).map (C2.val M) = E2V.bitsF N m := by
  rw [bitsF_eq, List.map_map]
  have hl : mb.length = m := by simpa [vs] using congrArg List.length h
  subst hl
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map] at h1
  have hj := congrArg (·.getD j 0) h
  simp only [vs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
    List.getElem?_eq_getElem h1, Option.map_some, Option.getD_some] at hj
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Lvm.Q2.kC2, C2.val, hzk, hj]
  exact bitE_c0 N j

/-- The value of a lane pair. -/
theorem laneC2_mk (a : Nat) : (Lvm.Q1.laneC2 a).val M = (⟨M.k a, M.k (a + 1)⟩ : FE2) := rfl

/-- A constant's value. -/
theorem const_val {τ : Ty} {k' : FK} {x : Cell} {p : Ptr} (h : SegsHold c M p (const τ k' x p).2) :
    (const τ k' x p).1.val M = FE.ofK k' := by
  have e := lin_spec (c := c) (M := M) (p := p) (τ := τ) (k := 1) (k' := k') (a := x) (b := x) h
  show (lin τ 1 k' x x p).1.val M = _
  rw [e, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

theorem powOkV_append {va : Nat → FE} {L1 L2 : List (Nat × Nat)} (h : Lvm.Q1.PowOkV va (L1 ++ L2)) :
    Lvm.Q1.PowOkV va L1 ∧ Lvm.Q1.PowOkV va L2 :=
  ⟨fun a ha => h a (List.mem_append_left _ ha), fun a ha => h a (List.mem_append_right _ ha)⟩

/-- `List.getD` of a mapped range. -/
theorem getD_map_range {α : Type} [Inhabited α] (f : Nat → α) {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i default = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- The `s'` bit cells paired with a `K` zero, in `E2` (`wire_phase`'s `hsbv`). -/
theorem sb_vals {C : QCfg} {zk : Cell} (hzk : zk.val M = 0) (s' : List FK)
    (hsb : ∀ i < 256, M.k (bsB C + i) = if sBitsD s' i then 1 else 0) :
    ((sbCells C).map fun b => Lvm.Q2.kC2 b zk).map (C2.val M) =
      (List.range 256).map fun p => E2V.bitF (sBitsD s' p) := by
  simp only [sbCells, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  simp only [Function.comp_apply, Lvm.Q2.kC2, C2.val, hzk, Cell.val_K, hsb i (List.mem_range.mp hi)]
  unfold E2V.bitF
  split <;> rfl

/-- `ok_bind` with the output: the bind's output is the continuation's at the next pointer. -/
theorem ok_bindE {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr} (h : Lvm.QSig.Ok c M (m >>= f) p) :
    ∃ q, Lvm.QSig.Ok c M m p ∧ Lvm.QSig.Ok c M (f (m p).1) q ∧ ((m >>= f) p).1 = (f (m p).1 q).1 := by
  obtain ⟨h1, h2, h3⟩ := Lvm.QSig.ok_bind' h
  exact ⟨_, h1, h2, h3⟩

/-- A row switch's seven `r''` cells hold the answers at `qr + 9 k`. -/
theorem rowG_rr {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {qr tB z o : Nat}
    (hT : qr + 9 * 6 + 2 < T) :
    Hs c M (Lvm.Q2.rowG qr tB z o)
      (fun ro => ro.rr.map (Cell.val M) = (List.range 7).map fun k => feAt sig (8 * (qr + 9 * k))) := by
  unfold Lvm.Q2.rowG
  refine hs_bind (Lvm.Q2.hs_mapBC _ (fun q => feAt sig (8 * q)) (Lvm.Q2.rowLanes qr) fun q hq =>
    Lvm.Q2.hs_loadLane hS (by
      simp only [Lvm.Q2.rowLanes, List.mem_map, List.mem_range] at hq; obtain ⟨k, hk, rfl⟩ := hq; (clear * - hT hk; omega)))
    fun rr hrr => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_pure ?_
  rw [hrr, Lvm.Q2.rowLanes, List.map_map]; rfl

/-- **A row switch's `ν` cells stand for its `eq(r'', ·)` cells** (`rowNuGL_ok` on `rowG`'s outputs; blob v4's looped
`ν`). -/
theorem rowNuOk_of {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {qr tB z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hT : qr + 9 * 6 + 2 < T) {p p' : Ptr} (h1 : SegsHold c M p (Lvm.Q2.rowG qr tB z o p).2)
    (h2 : SegsHold c M p' (Lvm.Q2.rowNuGL (Lvm.Q2.rowG qr tB z o p).1 z o p').2) :
    Lvm.Q2.RowNuOk M (Lvm.Q2.rowNuGL (Lvm.Q2.rowG qr tB z o p).1 z o p').1
      ((Lvm.Q2.rowG qr tB z o p).1.eqR.map (Cell.val M)) := by
  have hE := (Lvm.Q2.rowG_spec (c := c) hS hz ho hT p h1).1
  have hr := rowG_rr (c := c) hS (tB := tB) (z := z) (o := o) hT p h1
  have hrl : (Lvm.Q2.rowG qr tB z o p).1.rr.length = 7 := by
    have := congrArg List.length hr; simpa using this
  rw [hE]
  refine Lvm.Q2.rowNuGL_ok _ hz ho _ (by simp) hE ?_ h2
  rw [← Lvm.Har.getD_map_val _ (by (clear * - hrl; omega))]
  show ((Lvm.Q2.rowG qr tB z o p).1.rr.map (Cell.val M)).getD 6 0 = _
  rw [hr]

/-- `E`-shifted copies of cells `b + z` (`z` a zero) hold the cells' values. -/
theorem mapB_add_vs {z : Cell} (hz : z.val M = 0) (l : List Cell) :
    Hs c M (Lvm.Q2.mapB (fun b => add b z) l) (fun rs => vs M rs = vs M l) :=
  Lvm.Q2.hs_mapBC _ (Cell.val M) l fun a _ p h => by
    show (add a z p).1.val M = a.val M
    rw [add_val h, hz, add_zero]

/-- `mapB`'s outputs, by index. -/
theorem hs_mapB_getD {α β : Type} [Inhabited β] (f : α → BM β) (P : α → β → Prop) (hf : ∀ a, Hs c M (f a) (P a)) :
    ∀ l : List α, Hs c M (Lvm.Q2.mapB f l) (fun rs => ∀ i (h : i < l.length), P l[i] (rs.getD i default))
  | [] => hs_pure fun i h => absurd h (Nat.not_lt_zero _)
  | a :: l => hs_bind (hf a) fun r hr => hs_bind (hs_mapB_getD f P hf l) fun rs hrs => hs_pure fun i h => by
    cases i with
    | zero => exact hr
    | succ i => exact hrs i (by simp at h; (clear * - h; omega))

/-- A builder's output as an opaque value. -/
theorem ok_out {α : Type} {m : BM α} {p : Ptr} (_ : Lvm.QSig.Ok c M m p) : ∃ a, (m p).1 = a := ⟨_, rfl⟩

/-- A phase fact along equal programs and end positions. -/
theorem phaseAt_cast {α : Type} {F F' : DM α} {sig : ByteArray} {P P' P'' : Nat} {v : α}
    (h : Lvm.Har.PhaseAt F sig P P' v) (hF : F = F') (hP : P' = P'') : Lvm.Har.PhaseAt F' sig P P'' v := by
  subst hF hP; exact h

theorem map_getD_range {α β : Type} [Inhabited α] (f : ℕ → α) (g : α → β) (n : ℕ) :
    (List.range n).map (fun i => g (((List.range n).map f).getD i default)) = ((List.range n).map f).map g := by
  rw [List.map_map]
  exact List.map_congr_left fun i hi => by
    simp only [Function.comp_apply]; rw [getD_map_range f (List.mem_range.mp hi)]

/-- The gadgets' lane lookup is `laneOf`. -/
theorem getD_toArray (p : Params) (k : Nat) : (itemLanes p).toArray.getD k 0 = laneOf p k := by
  simp only [laneOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

end FrontGen

end Lvm.E2Q

-- ===== merged from `LvmE2QKLay` (lvm2 U-TAPE closure: `LvmE2QKLay.lean` is now a stub importing `LvmE2QHarGen`) =====
-- New for lvm2 E2F (E2F-QH4): the `E2` Keccak layer template's layout facts (`layOk2`), decided by the kernel per shape
-- (`P = 15`: the tape at P20; `P = 9`: `KS` at P20), as `LvmQKeccakGkr`'s `layOk_11`/`layOk_15` for `E3`.

/-!
# `layOk2` at the P20 shapes

The kernel decides `layOk2 P` on the RMFE literals (`projLit`, `embedLit`): `layOk2_eq_lit` rewrites it into
`layOk2T (layerTB2T projLit embedLit) P`, where `layerTB2T` is `layerTB2` with the two tables as parameters
(`layerTB2_eq_tbl`, by `rfl`) and `layOk2T T` is `layOk2` with `T` in place of `layerTB2` (`layOk2_eq_T`, by `rfl`).
The proofs then rewrite `layerTB2T` into `layerTB2F` (`layerTB2T_eq_F`) and `layOk2T` into `layOk2TR` (`layOk2T_eq_R`),
the same values in forms the kernel evaluates faster (GOLF's `layOk` scheme for `E3`, `LvmQKeccakGkr` on `lvm2/GOLF`).
-/


namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- `layerTB2` with the RMFE tables `pr` (`rmfeProject`), `em` (`rmfeEmbed`) as parameters. -/
def layerTB2T (pr em : List Nat) (c : LCfg) : TB Unit :=
  let str := [c.str2]
  let value := c.pv2 0
  let mu := (List.range 16).map fun i => c.pv2 (1 + i)
  let kappa := c.pv2 17
  let point := (List.range (c.P + 1)).map fun i => c.pv2 (18 + i)
  let B := (List.range 25).map fun l => c.pv2 (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv2 (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv2 (50 + c.P + i)
  let q := c.q
  let prod := (List.range productBits).map fun k => lane2 (q + 2 * k) str
  let s := lane2 (q + 104) str
  q2Base (.ext ⟨.K, q, str⟩) >>= fun base =>
  let zK := base.1
  let z := base.2.1
  let one := base.2.2
  q2Proj z pr mu prod >>= fun proj =>
  q2One (point.getD c.P default) >>= fun seg0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k i) zK, flips.getD i default)) >>= fun in0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k (7 + i)) zK, flips.getD i default)) >>= fun in1 =>
  q2Dot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  q2Mul iota kappa proj >>= fun e1 => q2Add e1 value >>= fun e1' => q2Assert e1' (c.k 15) >>= fun _ =>
  q2Inst z one s em >>= fun mk =>
  q2Horner s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  q2PackRounds z str (q + 113) point v0 one >>= fun pk =>
  q2LocalRounds str 11 (q + 113 + 14 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 289 + 14 * (c.P + 1)
  let t := (List.range 3).map fun k => lane2 (q3 + 2 * k) str
  let beta := lane2 (q3 + 7) str
  q2EqTab z [one] (lc.2.take 3) >>= fun tbLo => q2EqTab z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  q2EqTab z [one] (a.take 3) >>= fun taLo => q2EqTab z [one] (a.drop 3) >>= fun taHi =>
  q2EqTab z [one] (lc.2.drop 6) >>= fun eL =>
  mapT2 (q2LowTab z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapT2 (q2LowTab z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapT2 (q2HighTab z taHi tbHi) (List.range 8) >>= fun H =>
  mapT2 (q2Shift z L0 L1 H) (List.range 64) >>= fun sh =>
  q2SumMap z 25 (fun l => q2LaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    q2Mul (eL.getD l default) lf z) >>= fun Wk =>
  q2SumMap z 25 (fun l => q2Mul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  q2Index z 0 one (lc.2.take 6) >>= fun idx => q2Mul dfB idx z >>= fun Wf =>
  q2Add Wf Wk >>= fun d => q2Mul (kS2 (c.k 14) zK) d Wk >>= fun W =>
  q2Mul mk.2 (t.getD 0 default) z >>= fun kt0 => q2Add mk.2 (t.getD 1 default) >>= fun k1 =>
  q2Mul k1 (t.getD 2 default) kt0 >>= fun m => q2Mul pk.2.1 W z >>= fun sw => q2Mul sw m lc.1 >>= fun e2 =>
  q2Assert e2 (c.k 15) >>= fun _ =>
  q2Mul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => q2Mul beta tt (t.getD 0 default) >>= fun v' =>
  q2LaneW eL beta >>= fun B' =>
  q2EqTab z [one] (lc.2.take 6) >>= fun A' =>
  mapT2 (q2Flip z B' A') (List.range 7) >>= fun fl =>
  mapT2 q2Copy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

theorem layerTB2_eq_tbl : layerTB2 = layerTB2T rmfeProject rmfeEmbed := rfl

/-- `cbOf2` for the template builder `T`. -/
def cbOf2T (T : LCfg → TB Unit) (P : Nat) : Nat := (T ⟨P, 0, 0, 0⟩ 0).2.length - 2 * (57 + P)

/-- `lay02` for the template builder `T`. -/
def lay02T (T : LCfg → TB Unit) (P : Nat) : LCfg := ⟨P, 0, 0, cbOf2T T P⟩

/-- `layIns2` for the template builder `T`. -/
def layIns2T (T : LCfg → TB Unit) (P : Nat) : List Ins := (T (lay02T T P) 0).2

/-- `layOk2` for the template builder `T`. -/
def layOk2T (T : LCfg → TB Unit) (P : Nat) : Bool :=
  (layIns2T T P).length == cbOf2T T P + 2 * (57 + P) &&
  (layIns2T T P).all (fun i => i.op != .assert0 || i.args.getD 1 default == (lay02T T P).k 15) &&
  ((layIns2T T P).drop (cbOf2T T P)).all fun i => i.ty == .K && i.op != .assert0

theorem layOk2_eq_T (P : Nat) : layOk2 P = layOk2T layerTB2 P := rfl

theorem layOk2_eq_lit (P : Nat) : layOk2 P = layOk2T (layerTB2T projLit embedLit) P := by
  rw [layOk2_eq_T, layerTB2_eq_tbl, rmfeProject_eq, rmfeEmbed_eq]

/-! ## Fast evaluation of the layer template (proof help)

`mapT2` ends each step in `pure`, so its instructions are `l₀ ++ ((l₁ ++ (… ++ [])) ++ [])`: a kernel walk of the list
takes element `j` through `j` appends. The `F` copies build the same pair with every tail on the right (`mapT2_eq_F`
…, by induction, no evaluation); `layerTB2T_eq_F` puts them into the template before the kernel decides. -/

/-- `mapT2` with the tail on the right. -/
def mapT2F {α β : Type} (f : α → TB β) : List α → TB (List β)
  | [] => fun _ => ([], [])
  | a :: as => fun n =>
    let r := f a n
    let r' := mapT2F f as (n + r.2.length)
    (r.1 :: r'.1, r.2 ++ r'.2)

theorem mapT2_eq_F {α β : Type} : @mapT2 α β = @mapT2F α β := by
  funext f l n
  induction l generalizing n with
  | nil => rfl
  | cons a as ih => simp only [mapT2, mapT2F, tb_bind, tb_pure, ih, List.append_nil]

/-- `q2Powers` with the tail on the right. -/
def q2PowersF (z s : S2) : S2 → Nat → TB (List S2)
  | _, 0 => fun _ => ([], [])
  | acc, k + 1 => fun n =>
    let r := q2Mul acc s z n
    let r' := q2PowersF z s r.1 k (n + r.2.length)
    (acc :: r'.1, r.2 ++ r'.2)

theorem q2Powers_eq_F (z s : S2) : ∀ (acc : S2) (k : Nat), q2Powers z s acc k = q2PowersF z s acc k
  | _, 0 => rfl
  | acc, k + 1 => by
    funext n
    simp only [q2Powers, q2PowersF, tb_bind, tb_pure, q2Powers_eq_F z s _ k, List.append_nil]

/-- `q2SumMap` through `mapT2F`. -/
def q2SumMapF (z : S2) (k : Nat) (f : Nat → TB S2) : TB S2 :=
  mapT2F f (List.range k) >>= fun ts => q2Sum z ts

theorem q2SumMap_eq_F : q2SumMap = q2SumMapF := by
  funext z k f; simp only [q2SumMap, q2SumMapF, mapT2_eq_F]

/-- `q2Proj` through `q2SumMapF`. -/
def q2ProjF (z : S2) (masks : List Nat) (mu prod : List S2) : TB S2 :=
  q2SumMapF z prod.length fun c => q2Sum z (projSrcs2 masks mu c) >>= fun P => q2Mul P (prod.getD c default) z

theorem q2Proj_eq_F : q2Proj = q2ProjF := by
  funext z masks mu prod; simp only [q2Proj, q2ProjF, q2SumMap_eq_F]

/-- `q2Inst` through `q2PowersF`, `mapT2F`. -/
def q2InstF (z one s : S2) (embs : List Nat) : TB (List S2 × S2) :=
  q2PowersF z s one embedBits >>= fun pw => mapT2F (fun e => q2Sum z (embSrcs2 pw e)) embs >>= fun mu =>
    q2Sum z mu >>= fun kappa => pure (mu, kappa)

theorem q2Inst_eq_F : q2Inst = q2InstF := by
  funext z one s embs; simp only [q2Inst, q2InstF, q2Powers_eq_F, mapT2_eq_F]

/-- `q2EqStep` through `mapT2F`. -/
def q2EqStepF (z : S2) (tab : List S2) (r : S2) : TB (List S2) :=
  q2One r >>= fun r1 => mapT2F (fun e => q2Mul e r1 z) tab >>= fun lo =>
    mapT2F (fun e => q2Mul e r z) tab >>= fun hi => pure (lo ++ hi)

/-- `q2EqTab` through `q2EqStepF`. -/
def q2EqTabF (z : S2) : List S2 → List S2 → TB (List S2)
  | tab, [] => pure tab
  | tab, r :: rs => q2EqStepF z tab r >>= fun t => q2EqTabF z t rs

theorem q2EqTab_eq_F (z : S2) : ∀ (tab pt : List S2), q2EqTab z tab pt = q2EqTabF z tab pt
  | _, [] => rfl
  | tab, r :: rs => by
    have e : q2EqStep z tab r = q2EqStepF z tab r := by simp only [q2EqStep, q2EqStepF, mapT2_eq_F]
    simp only [q2EqTab, q2EqTabF, e, q2EqTab_eq_F z _ rs]

/-- `q2LowTab` through `q2SumMapF`. -/
def q2LowTabF (z : S2) (ta tb : List S2) (c rl : Nat) : TB S2 :=
  q2SumMapF z 8 fun zz => if (zz + rl) / 8 = c then q2Mul (tb.getD zz default) (ta.getD ((zz + rl) % 8) default) z
    else pure z

theorem q2LowTab_eq_F : q2LowTab = q2LowTabF := by
  funext z ta tb c rl; simp only [q2LowTab, q2LowTabF, q2SumMap_eq_F]

/-- `q2HighTab` through `q2SumMapF`. -/
def q2HighTabF (z : S2) (ta tb : List S2) (k : Nat) : TB S2 :=
  q2SumMapF z 8 fun zz => q2Mul (tb.getD zz default) (ta.getD ((zz + k) % 8) default) z

theorem q2HighTab_eq_F : q2HighTab = q2HighTabF := by
  funext z ta tb k; simp only [q2HighTab, q2HighTabF, q2SumMap_eq_F]

/-- `q2LaneW` through `mapT2F`. -/
def q2LaneWF (eL : List S2) (beta : S2) : TB (List S2) :=
  mapT2F (fun l => q2Mul beta (eL.getD (keccakAlong (64 * l) 3 / 64) default)
    (eL.getD (keccakAlong (64 * l) 4 / 64) default) >>= fun u => q2Mul beta u (eL.getD l default)) (List.range 25)

theorem q2LaneW_eq_F : q2LaneW = q2LaneWF := by
  funext eL beta; simp only [q2LaneW, q2LaneWF, mapT2_eq_F]

/-- `layerTB2T` through the `F` gadgets. -/
def layerTB2F (pr em : List Nat) (c : LCfg) : TB Unit :=
  let str := [c.str2]
  let value := c.pv2 0
  let mu := (List.range 16).map fun i => c.pv2 (1 + i)
  let kappa := c.pv2 17
  let point := (List.range (c.P + 1)).map fun i => c.pv2 (18 + i)
  let B := (List.range 25).map fun l => c.pv2 (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv2 (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv2 (50 + c.P + i)
  let q := c.q
  let prod := (List.range productBits).map fun k => lane2 (q + 2 * k) str
  let s := lane2 (q + 104) str
  q2Base (.ext ⟨.K, q, str⟩) >>= fun base =>
  let zK := base.1
  let z := base.2.1
  let one := base.2.2
  q2ProjF z pr mu prod >>= fun proj =>
  q2One (point.getD c.P default) >>= fun seg0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k i) zK, flips.getD i default)) >>= fun in0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k (7 + i)) zK, flips.getD i default)) >>= fun in1 =>
  q2Dot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  q2Mul iota kappa proj >>= fun e1 => q2Add e1 value >>= fun e1' => q2Assert e1' (c.k 15) >>= fun _ =>
  q2InstF z one s em >>= fun mk =>
  q2Horner s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  q2PackRounds z str (q + 113) point v0 one >>= fun pk =>
  q2LocalRounds str 11 (q + 113 + 14 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 289 + 14 * (c.P + 1)
  let t := (List.range 3).map fun k => lane2 (q3 + 2 * k) str
  let beta := lane2 (q3 + 7) str
  q2EqTabF z [one] (lc.2.take 3) >>= fun tbLo => q2EqTabF z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  q2EqTabF z [one] (a.take 3) >>= fun taLo => q2EqTabF z [one] (a.drop 3) >>= fun taHi =>
  q2EqTabF z [one] (lc.2.drop 6) >>= fun eL =>
  mapT2F (q2LowTabF z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapT2F (q2LowTabF z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapT2F (q2HighTabF z taHi tbHi) (List.range 8) >>= fun H =>
  mapT2F (q2Shift z L0 L1 H) (List.range 64) >>= fun sh =>
  q2SumMapF z 25 (fun l => q2LaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    q2Mul (eL.getD l default) lf z) >>= fun Wk =>
  q2SumMapF z 25 (fun l => q2Mul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  q2Index z 0 one (lc.2.take 6) >>= fun idx => q2Mul dfB idx z >>= fun Wf =>
  q2Add Wf Wk >>= fun d => q2Mul (kS2 (c.k 14) zK) d Wk >>= fun W =>
  q2Mul mk.2 (t.getD 0 default) z >>= fun kt0 => q2Add mk.2 (t.getD 1 default) >>= fun k1 =>
  q2Mul k1 (t.getD 2 default) kt0 >>= fun m => q2Mul pk.2.1 W z >>= fun sw => q2Mul sw m lc.1 >>= fun e2 =>
  q2Assert e2 (c.k 15) >>= fun _ =>
  q2Mul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => q2Mul beta tt (t.getD 0 default) >>= fun v' =>
  q2LaneWF eL beta >>= fun B' =>
  q2EqTabF z [one] (lc.2.take 6) >>= fun A' =>
  mapT2F (q2Flip z B' A') (List.range 7) >>= fun fl =>
  mapT2F q2Copy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

theorem layerTB2T_eq_F : layerTB2T = layerTB2F := by
  funext pr em c
  simp only [layerTB2T, layerTB2F, mapT2_eq_F, q2Proj_eq_F, q2Inst_eq_F, q2EqTab_eq_F, q2LowTab_eq_F,
    q2HighTab_eq_F, q2SumMap_eq_F, q2LaneW_eq_F]

/-- `List.length` by the recursor (proof help: the kernel reduces it without the structural-recursion wrappers;
GOLF's `lenR`). -/
def lenR2 {α : Type} (l : List α) : Nat := List.rec 0 (fun _ _ n => n + 1) l

/-- `List.all` by the recursor. -/
def allR2 {α : Type} (p : α → Bool) (l : List α) : Bool := List.rec true (fun a _ r => p a && r) l

/-- `List.drop` through the recursor. -/
def dropR2 {α : Type} : Nat → List α → List α
  | 0, l => l
  | n + 1, l => List.rec [] (fun _ t _ => dropR2 n t) l

theorem lenR2_eq {α : Type} (l : List α) : lenR2 l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (· + 1) ih

theorem allR2_eq {α : Type} (p : α → Bool) (l : List α) : allR2 p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a l ih => exact (congrArg (p a && ·) ih).trans (List.all_cons).symm

theorem dropR2_eq {α : Type} : ∀ (n : Nat) (l : List α), dropR2 n l = l.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: t => dropR2_eq n t

/-- `cbOf2T` through `lenR2`. -/
def cbOf2TR (T : LCfg → TB Unit) (P : Nat) : Nat := lenR2 (T ⟨P, 0, 0, 0⟩ 0).2 - 2 * (57 + P)

/-- `layOk2T` through `lenR2`, `allR2`, `dropR2` (`layOk2T_eq_R`), the form the kernel decides. -/
def layOk2TR (T : LCfg → TB Unit) (P : Nat) : Bool :=
  lenR2 (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2 == cbOf2TR T P + 2 * (57 + P) &&
  allR2 (fun i => i.op != .assert0 || i.args.getD 1 default == (LCfg.mk P 0 0 (cbOf2TR T P)).k 15)
    (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2 &&
  allR2 (fun i => i.ty == .K && i.op != .assert0) (dropR2 (cbOf2TR T P) (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2)

theorem layOk2T_eq_R (T : LCfg → TB Unit) (P : Nat) : layOk2T T P = layOk2TR T P := by
  simp only [layOk2T, layOk2TR, layIns2T, lay02T, cbOf2T, cbOf2TR, lenR2_eq, allR2_eq, dropR2_eq]

/-! ## The template by recursors (proof help)

The `F` template still pays, per instruction, `TB`'s instance `bind` and the structural-recursion wrappers of
`List.length`, `List.append` and the gadgets. The `R` copies (`layerTB2F_eq_R`, by induction, no evaluation) bind by
`bindR` (`lenR2`, `appR2`) and recurse by `List.rec`/`Nat.rec`; the kernel then decides `layOk2` on `layerTB2R`. -/

/-- `List.append` by the recursor. -/
def appR2 {α : Type} (l l' : List α) : List α := List.rec l' (fun a _ r => a :: r) l

theorem appR2_eq {α : Type} (l l' : List α) : appR2 l l' = l ++ l' := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

/-- `TB`'s bind through `lenR2`, `appR2`. -/
def bindR {α β : Type} (m : TB α) (f : α → TB β) : TB β := fun n =>
  let r := m n
  let r' := f r.1 (n + lenR2 r.2)
  (r'.1, appR2 r.2 r'.2)

theorem bind_eq_R {α β : Type} (m : TB α) (f : α → TB β) : m >>= f = bindR m f := by
  funext n; rw [tb_bind]; simp only [bindR, lenR2_eq, appR2_eq]

/-- `mapT2F` by the recursor. -/
def mapT2R {α β : Type} (f : α → TB β) (l : List α) : TB (List β) :=
  List.rec (motive := fun _ => TB (List β)) (fun _ => ([], [])) (fun a _ ih => fun n =>
    let r := f a n
    let r' := ih (n + lenR2 r.2)
    (r.1 :: r'.1, appR2 r.2 r'.2)) l

theorem mapT2F_eq_R {α β : Type} : @mapT2F α β = @mapT2R α β := by
  funext f l n
  induction l generalizing n with
  | nil => rfl
  | cons a as ih =>
    show _ = (let r := f a n; let r' := mapT2R f as (n + lenR2 r.2); (r.1 :: r'.1, appR2 r.2 r'.2))
    simp only [mapT2F, ih, lenR2_eq, appR2_eq]

/-- `q2Sum` by the recursor. -/
def q2SumR (s : S2) (cs : List S2) : TB S2 :=
  List.rec (motive := fun _ => S2 → TB S2) (fun s => pure s) (fun c _ ih s => bindR (q2Add s c) ih) cs s

theorem q2Sum_eq_R : q2Sum = q2SumR := by
  funext s cs
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    show _ = bindR (q2Add s c) fun s' => q2SumR s' cs
    simp only [q2Sum, bind_eq_R, ih]

/-- `q2Dot` by the recursor. -/
def q2DotR (acc : S2) (l : List (S2 × S2)) : TB S2 :=
  List.rec (motive := fun _ => S2 → TB S2) (fun acc => pure acc)
    (fun cd _ ih acc => bindR (q2Mul cd.1 cd.2 acc) ih) l acc

theorem q2Dot_eq_R : q2Dot = q2DotR := by
  funext acc l
  induction l generalizing acc with
  | nil => rfl
  | cons cd l ih =>
    show _ = bindR (q2Mul cd.1 cd.2 acc) fun a => q2DotR a l
    simp only [q2Dot, bind_eq_R, ih]

/-- `q2Horner` by the recursor. -/
def q2HornerR (x h : S2) (l : List S2) : TB S2 :=
  List.rec (motive := fun _ => S2 → TB S2) (fun h => pure h) (fun c _ ih h => bindR (q2Mul h x c) ih) l h

theorem q2Horner_eq_R : q2Horner = q2HornerR := by
  funext x h l
  induction l generalizing h with
  | nil => rfl
  | cons c l ih =>
    show _ = bindR (q2Mul h x c) fun h' => q2HornerR x h' l
    simp only [q2Horner, bind_eq_R, ih]

/-- `q2EqStepF` through `bindR`, `mapT2R`. -/
def q2EqStepR (z : S2) (tab : List S2) (r : S2) : TB (List S2) :=
  bindR (q2One r) fun r1 => bindR (mapT2R (fun e => q2Mul e r1 z) tab) fun lo =>
    bindR (mapT2R (fun e => q2Mul e r z) tab) fun hi => pure (lo ++ hi)

/-- `q2EqTabF` by the recursor. -/
def q2EqTabR (z : S2) (tab pt : List S2) : TB (List S2) :=
  List.rec (motive := fun _ => List S2 → TB (List S2)) (fun tab => pure tab)
    (fun r _ ih tab => bindR (q2EqStepR z tab r) ih) pt tab

theorem q2EqTabF_eq_R : q2EqTabF = q2EqTabR := by
  funext z tab pt
  induction pt generalizing tab with
  | nil => rfl
  | cons r rs ih =>
    show _ = bindR (q2EqStepR z tab r) fun t => q2EqTabR z t rs
    simp only [q2EqTabF, q2EqStepF, q2EqStepR, bind_eq_R, mapT2F_eq_R, ih]

/-- `q2PowersF` by the recursor. -/
def q2PowersR (z s acc : S2) (k : Nat) : TB (List S2) :=
  Nat.rec (motive := fun _ => S2 → TB (List S2)) (fun _ _ => ([], [])) (fun _ ih acc => fun n =>
    let r := q2Mul acc s z n
    let r' := ih r.1 (n + lenR2 r.2)
    (acc :: r'.1, appR2 r.2 r'.2)) k acc

theorem q2PowersF_eq_R : q2PowersF = q2PowersR := by
  funext z s acc k
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    funext n
    show _ = (let r := q2Mul acc s z n; let r' := q2PowersR z s r.1 k (n + lenR2 r.2);
      (acc :: r'.1, appR2 r.2 r'.2))
    simp only [q2PowersF, ih, lenR2_eq, appR2_eq]

/-- `q2SumMapF` through `mapT2R`, `q2SumR`. -/
def q2SumMapR (z : S2) (k : Nat) (f : Nat → TB S2) : TB S2 :=
  bindR (mapT2R f (List.range k)) fun ts => q2SumR z ts

theorem q2SumMapF_eq_R : q2SumMapF = q2SumMapR := by
  funext z k f; simp only [q2SumMapF, q2SumMapR, bind_eq_R, mapT2F_eq_R, q2Sum_eq_R]

/-- `q2ProjF` through `q2SumMapR`. -/
def q2ProjR (z : S2) (masks : List Nat) (mu prod : List S2) : TB S2 :=
  q2SumMapR z prod.length fun c => bindR (q2SumR z (projSrcs2 masks mu c)) fun P => q2Mul P (prod.getD c default) z

theorem q2ProjF_eq_R : q2ProjF = q2ProjR := by
  funext z masks mu prod; simp only [q2ProjF, q2ProjR, q2SumMapF_eq_R, bind_eq_R, q2Sum_eq_R]

/-- `q2InstF` through the `R` gadgets. -/
def q2InstR (z one s : S2) (embs : List Nat) : TB (List S2 × S2) :=
  bindR (q2PowersR z s one embedBits) fun pw => bindR (mapT2R (fun e => q2SumR z (embSrcs2 pw e)) embs) fun mu =>
    bindR (q2SumR z mu) fun kappa => pure (mu, kappa)

theorem q2InstF_eq_R : q2InstF = q2InstR := by
  funext z one s embs; simp only [q2InstF, q2InstR, bind_eq_R, q2PowersF_eq_R, mapT2F_eq_R, q2Sum_eq_R]

/-- `q2LowTabF` through `q2SumMapR`. -/
def q2LowTabR (z : S2) (ta tb : List S2) (c rl : Nat) : TB S2 :=
  q2SumMapR z 8 fun zz => if (zz + rl) / 8 = c then q2Mul (tb.getD zz default) (ta.getD ((zz + rl) % 8) default) z
    else pure z

theorem q2LowTabF_eq_R : q2LowTabF = q2LowTabR := by
  funext z ta tb c rl; simp only [q2LowTabF, q2LowTabR, q2SumMapF_eq_R]

/-- `q2HighTabF` through `q2SumMapR`. -/
def q2HighTabR (z : S2) (ta tb : List S2) (k : Nat) : TB S2 :=
  q2SumMapR z 8 fun zz => q2Mul (tb.getD zz default) (ta.getD ((zz + k) % 8) default) z

theorem q2HighTabF_eq_R : q2HighTabF = q2HighTabR := by
  funext z ta tb k; simp only [q2HighTabF, q2HighTabR, q2SumMapF_eq_R]

/-- `q2Shift` through `bindR`. -/
def q2ShiftR (z : S2) (L0 L1 H : List S2) (r : Nat) : TB S2 :=
  bindR (q2Mul (L1.getD (r % 8) default) (H.getD ((r / 8 + 1) % 8) default) z) fun t =>
    q2Mul (L0.getD (r % 8) default) (H.getD (r / 8) default) t

theorem q2Shift_eq_R : q2Shift = q2ShiftR := by
  funext z L0 L1 H r; simp only [q2Shift, q2ShiftR, bind_eq_R]

/-- `q2LaneForm` through `bindR`, `q2DotR`. -/
def q2LaneFormR (z : S2) (B : List S2) (R : Nat → S2) (l : Nat) : TB S2 :=
  bindR (q2Mul (B.getD (keccakPi l) default) (R (rho l)) z) fun t1 =>
  bindR (q2DotR t1 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) default, R (rho ((l % 5 + 1) % 5 + 5 * y))))) fun t2 =>
  q2DotR t2 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) default, R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

theorem q2LaneForm_eq_R : q2LaneForm = q2LaneFormR := by
  funext z B R l; simp only [q2LaneForm, q2LaneFormR, bind_eq_R, q2Dot_eq_R]

/-- `q2Flip` through `q2LaneFormR`. -/
def q2FlipR (z : S2) (B A : List S2) (i : Nat) : TB S2 :=
  q2LaneFormR z B (fun s => A.getD ((iotaPos i + s) % 64) default) 0

theorem q2Flip_eq_R : q2Flip = q2FlipR := by
  funext z B A i; simp only [q2Flip, q2FlipR, q2LaneForm_eq_R]

/-- `q2IndexStep` through `bindR`. -/
def q2IndexStepR (z : S2) (k : Nat) (acc r : S2) : TB S2 :=
  bindR (q2Scale (1 + FK.x ^ (2 ^ k)) r) fun u => bindR (q2One u) fun w => q2Mul acc w z

/-- `q2Index` by the recursor. -/
def q2IndexR (z : S2) (k : Nat) (acc : S2) (rs : List S2) : TB S2 :=
  List.rec (motive := fun _ => Nat → S2 → TB S2) (fun _ acc => pure acc)
    (fun r _ ih k acc => bindR (q2IndexStepR z k acc r) (ih (k + 1))) rs k acc

theorem q2Index_eq_R : q2Index = q2IndexR := by
  funext z k acc rs
  induction rs generalizing k acc with
  | nil => rfl
  | cons r rs ih =>
    show _ = bindR (q2IndexStepR z k acc r) fun acc' => q2IndexR z (k + 1) acc' rs
    simp only [q2Index, q2IndexStep, q2IndexStepR, bind_eq_R, ih]

/-- `q2LaneWF` through `mapT2R`, `bindR`. -/
def q2LaneWR (eL : List S2) (beta : S2) : TB (List S2) :=
  mapT2R (fun l => bindR (q2Mul beta (eL.getD (keccakAlong (64 * l) 3 / 64) default)
    (eL.getD (keccakAlong (64 * l) 4 / 64) default)) fun u => q2Mul beta u (eL.getD l default)) (List.range 25)

theorem q2LaneWF_eq_R : q2LaneWF = q2LaneWR := by
  funext eL beta; simp only [q2LaneWF, q2LaneWR, mapT2F_eq_R, bind_eq_R]

/-- `q2Base` through `bindR`. -/
def q2BaseR (b : Src) : TB (Src × S2 × S2) :=
  bindR (kLin 1 0 b b) fun zK => bindR (kLin 0 1 zK zK) fun oK => pure (zK, (zK, zK), (oK, zK))

theorem q2Base_eq_R : q2Base = q2BaseR := by
  funext b; simp only [q2Base, q2BaseR, bind_eq_R]

/-- `q2Assert` through `bindR`. -/
def q2AssertR (a : S2) (gate : Src) : TB Unit := bindR (gAssert a.1 gate) fun _ => gAssert a.2 gate

theorem q2Assert_eq_R : q2Assert = q2AssertR := by
  funext a gate; simp only [q2Assert, q2AssertR, bind_eq_R]

/-- `q2PackRound` through `bindR`. -/
def q2PackRoundR (z : S2) (q : Nat) (str : List Nat) (r value scale : S2) : TB (S2 × S2 × S2) :=
  let c1 := lane2 q str
  let c2 := lane2 (q + 2) str
  let ch := lane2 (q + 5) str
  bindR (q2Add c1 c2) fun s => bindR (q2Mul r s value) fun c0 => bindR (q2Mul c2 ch c1) fun h =>
  bindR (q2Mul h ch c0) fun pe => bindR (q2Lin 1 1 r ch) fun g => bindR (q2Mul g pe z) fun v' =>
  bindR (q2Mul scale g z) fun s' => pure (v', s', ch)

/-- `q2PackRounds` by the recursor. -/
def q2PackRoundsR (z : S2) (str : List Nat) (q : Nat) (pt : List S2) (value scale : S2) : TB (S2 × S2 × List S2) :=
  List.rec (motive := fun _ => Nat → S2 → S2 → TB (S2 × S2 × List S2)) (fun _ value scale => pure (value, scale, []))
    (fun r _ ih q value scale => bindR (q2PackRoundR z q str r value scale) fun a =>
      bindR (ih (q + 14) a.1 a.2.1) fun b => pure (b.1, b.2.1, a.2.2 :: b.2.2)) pt q value scale

theorem q2PackRounds_eq_R : q2PackRounds = q2PackRoundsR := by
  funext z str q pt value scale
  induction pt generalizing q value scale with
  | nil => rfl
  | cons r rs ih =>
    show _ = bindR (q2PackRoundR z q str r value scale) fun a =>
      bindR (q2PackRoundsR z str (q + 14) rs a.1 a.2.1) fun b => pure (b.1, b.2.1, a.2.2 :: b.2.2)
    simp only [q2PackRounds, q2PackRound, q2PackRoundR, bind_eq_R, ih]

/-- `q2LocalRound` through `bindR`. -/
def q2LocalRoundR (q : Nat) (str : List Nat) (value : S2) : TB (S2 × S2) :=
  let c0 := lane2 q str
  let c2 := lane2 (q + 2) str
  let c3 := lane2 (q + 4) str
  let ch := lane2 (q + 7) str
  bindR (q2Add value c2) fun s => bindR (q2Add s c3) fun c1 =>
  bindR (q2Mul c3 ch c2) fun h1 => bindR (q2Mul h1 ch c1) fun h2 => bindR (q2Mul h2 ch c0) fun h3 => pure (h3, ch)

/-- `q2LocalRounds` by the recursor. -/
def q2LocalRoundsR (str : List Nat) (k q : Nat) (value : S2) : TB (S2 × List S2) :=
  Nat.rec (motive := fun _ => Nat → S2 → TB (S2 × List S2)) (fun _ value => pure (value, []))
    (fun _ ih q value => bindR (q2LocalRoundR q str value) fun a =>
      bindR (ih (q + 16) a.1) fun b => pure (b.1, a.2 :: b.2)) k q value

theorem q2LocalRounds_eq_R : q2LocalRounds = q2LocalRoundsR := by
  funext str k q value
  induction k generalizing q value with
  | zero => rfl
  | succ k ih =>
    show _ = bindR (q2LocalRoundR q str value) fun a =>
      bindR (q2LocalRoundsR str k (q + 16) a.1) fun b => pure (b.1, a.2 :: b.2)
    simp only [q2LocalRounds, q2LocalRound, q2LocalRoundR, bind_eq_R, ih]

/-- `layerTB2F` through the `R` gadgets and `bindR`. -/
def layerTB2R (pr em : List Nat) (c : LCfg) : TB Unit :=
  let str := [c.str2]
  let value := c.pv2 0
  let mu := (List.range 16).map fun i => c.pv2 (1 + i)
  let kappa := c.pv2 17
  let point := (List.range (c.P + 1)).map fun i => c.pv2 (18 + i)
  let B := (List.range 25).map fun l => c.pv2 (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv2 (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv2 (50 + c.P + i)
  let q := c.q
  let prod := (List.range productBits).map fun k => lane2 (q + 2 * k) str
  let s := lane2 (q + 104) str
  bindR (q2BaseR (.ext ⟨.K, q, str⟩)) fun base =>
  let zK := base.1
  let z := base.2.1
  let one := base.2.2
  bindR (q2ProjR z pr mu prod) fun proj =>
  bindR (q2One (point.getD c.P default)) fun seg0 =>
  bindR (q2DotR z ((List.range 7).map fun i => (kS2 (c.k i) zK, flips.getD i default))) fun in0 =>
  bindR (q2DotR z ((List.range 7).map fun i => (kS2 (c.k (7 + i)) zK, flips.getD i default))) fun in1 =>
  bindR (q2DotR z [(seg0, in0), (point.getD c.P default, in1)]) fun iota =>
  bindR (q2Mul iota kappa proj) fun e1 => bindR (q2Add e1 value) fun e1' => bindR (q2AssertR e1' (c.k 15)) fun _ =>
  bindR (q2InstR z one s em) fun mk =>
  bindR (q2HornerR s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default)) fun v0 =>
  bindR (q2PackRoundsR z str (q + 113) point v0 one) fun pk =>
  bindR (q2LocalRoundsR str 11 (q + 113 + 14 * (c.P + 1)) pk.1) fun lc =>
  let q3 := q + 289 + 14 * (c.P + 1)
  let t := (List.range 3).map fun k => lane2 (q3 + 2 * k) str
  let beta := lane2 (q3 + 7) str
  bindR (q2EqTabR z [one] (lc.2.take 3)) fun tbLo => bindR (q2EqTabR z [one] ((lc.2.drop 3).take 3)) fun tbHi =>
  bindR (q2EqTabR z [one] (a.take 3)) fun taLo => bindR (q2EqTabR z [one] (a.drop 3)) fun taHi =>
  bindR (q2EqTabR z [one] (lc.2.drop 6)) fun eL =>
  bindR (mapT2R (q2LowTabR z taLo tbLo 0) (List.range 8)) fun L0 =>
  bindR (mapT2R (q2LowTabR z taLo tbLo 1) (List.range 8)) fun L1 =>
  bindR (mapT2R (q2HighTabR z taHi tbHi) (List.range 8)) fun H =>
  bindR (mapT2R (q2ShiftR z L0 L1 H) (List.range 64)) fun sh =>
  bindR (q2SumMapR z 25 (fun l => bindR (q2LaneFormR z B (fun r => sh.getD r default) l) fun lf =>
    q2Mul (eL.getD l default) lf z)) fun Wk =>
  bindR (q2SumMapR z 25 (fun l => q2Mul (eL.getD l default) (B.getD l default) z)) fun dfB =>
  bindR (q2IndexR z 0 one (lc.2.take 6)) fun idx => bindR (q2Mul dfB idx z) fun Wf =>
  bindR (q2Add Wf Wk) fun d => bindR (q2Mul (kS2 (c.k 14) zK) d Wk) fun W =>
  bindR (q2Mul mk.2 (t.getD 0 default) z) fun kt0 => bindR (q2Add mk.2 (t.getD 1 default)) fun k1 =>
  bindR (q2Mul k1 (t.getD 2 default) kt0) fun m => bindR (q2Mul pk.2.1 W z) fun sw => bindR (q2Mul sw m lc.1) fun e2 =>
  bindR (q2AssertR e2 (c.k 15)) fun _ =>
  bindR (q2Mul beta (t.getD 2 default) (t.getD 1 default)) fun tt => bindR (q2Mul beta tt (t.getD 0 default)) fun v' =>
  bindR (q2LaneWR eL beta) fun B' =>
  bindR (q2EqTabR z [one] (lc.2.take 6)) fun A' =>
  bindR (mapT2R (q2FlipR z B' A') (List.range 7)) fun fl =>
  bindR (mapT2R q2Copy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl)) fun _ => pure ()


theorem layerTB2F_eq_R : layerTB2F = layerTB2R := by
  funext pr em c
  simp only [layerTB2F, layerTB2R, bind_eq_R, mapT2F_eq_R, q2ProjF_eq_R, q2InstF_eq_R, q2EqTabF_eq_R,
    q2LowTabF_eq_R, q2HighTabF_eq_R, q2SumMapF_eq_R, q2LaneWF_eq_R, q2Base_eq_R, q2Dot_eq_R, q2Assert_eq_R,
    q2Horner_eq_R, q2PackRounds_eq_R, q2LocalRounds_eq_R, q2Shift_eq_R, q2LaneForm_eq_R, q2Index_eq_R, q2Flip_eq_R]

/-- `op = assert0` by one `match` (proof help: the derived `DecidableEq Op` costs the kernel more per row). -/
def isA0 : Op → Bool
  | .assert0 => true
  | _ => false

/-- `ty = K` by one `match` (proof help). -/
def isKt : Ty → Bool
  | .K => true
  | .E => false

theorem op_bne (o : Op) : (o != Op.assert0) = !isA0 o := by cases o <;> rfl

theorem ty_beq (t : Ty) : (t == Ty.K) = isKt t := by cases t <;> rfl

/-- `layOk2TR` through `isA0`, `isKt` (`layOk2TR_eq_S`), the form the kernel decides. -/
def layOk2TS (T : LCfg → TB Unit) (P : Nat) : Bool :=
  lenR2 (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2 == cbOf2TR T P + 2 * (57 + P) &&
  allR2 (fun i => !isA0 i.op || i.args.getD 1 default == (LCfg.mk P 0 0 (cbOf2TR T P)).k 15)
    (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2 &&
  allR2 (fun i => isKt i.ty && !isA0 i.op) (dropR2 (cbOf2TR T P) (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2)

theorem layOk2TR_eq_S (T : LCfg → TB Unit) (P : Nat) : layOk2TR T P = layOk2TS T P := by
  simp only [layOk2TR, layOk2TS, op_bne, ty_beq]

-- `layOk2_15`, `layOk2_9` are in `LvmE2QHarFront` (S2GF/S2GT only; lvm2 U-TAPE).

end Lvm.Q1

-- ===== merged from `LvmE2QHarClaims` (lvm2 U-TAPE closure: `LvmE2QHarClaims.lean` is now a stub importing `LvmE2QHarGen`) =====
-- New for lvm2 E2-FT (E2F-C7): the front's claims stand for V's (`FRelZ`), generic in the cells' values: the `D` word
-- halves of the tape, the `E2` halves of `KS` and the link (for `front_phasesF`).

/-!
# The front's claims and V's

* **`forall₂_flatMap`**: `Forall₂` of two `flatMap`s over one list, element by element.
* **`selC2_vals`**, **`selC2_K`**: the selector cells hold `selPtF`, on `K` cells.
* **`dhalf_rel`**, **`dhalves_rel`**: the tape's `D` word halves (`FClaim.dhalf`) stand for V's split claims with the
  tails `tailDE2`.
* **`half_rel`**, **`halves_rel`**: an `E2` sum claim's halves stand for V's split claim (regular blocks, tail `0`).
* **`bound_rel`**: a boundary claim `D̃_l(bits(n − 1) ‖ l) = h_l` (tail `0`: `tailD_small` for `n ≤ 2^18`).
* **`frontCsF`**, **`front_claimsG`**: `frontF`'s claim list over its gadgets' outputs as variables, and the whole
  list stands for `frontClaimsD p` at a `p` with `P20`'s front facts (`RegsP`, `DselP`) (tape, `KS`, its outputs, the link), so that `front_phasesF` meets no builder
  run in the claims.
-/


namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q2 Lvm.QShape

variable {M : Mem}

theorem forall₂_flatMap {α β γ : Type} {R : β → γ → Prop} {f : α → List β} {g : α → List γ} :
    ∀ (L : List α), (∀ a ∈ L, List.Forall₂ R (f a) (g a)) → List.Forall₂ R (L.flatMap f) (L.flatMap g)
  | [], _ => .nil
  | a :: L, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h a (List.mem_cons_self ..)) (forall₂_flatMap L fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The selector cells hold `selPtF`. -/
theorem selC2_vals {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (sel len : ℕ) :
    (selC2 F sel len).map (C2.val M) = E2V.selPtF sel len := by
  simp only [selC2, E2V.selPtF, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  by_cases h : (sel >>> i) % 2 = 1 <;> simp [h, ho2, hz2]

theorem selC2_K {F : FCtx} (hz2 : KC2 F.z2) (ho2 : KC2 F.o2) (sel len : ℕ) : ∀ x ∈ selC2 F sel len, KC2 x := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  split
  · exact ho2
  · exact hz2

theorem selC2_length (F : FCtx) (sel len : ℕ) : (selC2 F sel len).length = len := by simp [selC2]

/-- A `K` cell pair's halves are its value's coordinates. -/
theorem kre_val {x : C2} (hx : KC2 x) : x.re.val M = FE.ofK (x.val M).re := (kcell_val hx.1).symm
theorem kim_val {x : C2} (hx : KC2 x) : x.im.val M = FE.ofK (x.val M).im := (kcell_val hx.2).symm

/-- **One `D` word claim's halves** (lane `l`, value cells `w`) stand for V's split claims with tails `tailDE2`. -/
theorem dhalf_rel {zc : Cell} {b : Bool} {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (hz2K : KC2 F.z2)
    (ho2K : KC2 F.o2) {r : List C2} (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) {l : ℕ} (hl : l < 4) {w : C2}
    (hw : KC2 w) :
    List.Forall₂ (FRelZ M zc b) [.dhalf false (r ++ selC2 F l 2) w.re, .dhalf true (r ++ selC2 F l 2) w.im]
      (((splitD 23 [(1, ⟨22, 0⟩, r.map (C2.val M) ++ E2V.selPtF l 2)] (w.val M)).zip
        (tailDE2 (r.map (C2.val M)) l)).map fun e => (Com.main, e.1, e.2)) := by
  have hz : (r ++ selC2 F l 2).map (C2.val M) = r.map (C2.val M) ++ E2V.selPtF l 2 := by
    rw [List.map_append, selC2_vals hz2 ho2]
  have hK : ∀ x ∈ r ++ selC2 F l 2, KC2 x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hr x h
    · exact selC2_K hz2K ho2K l 2 x h
  have hlen : (r ++ selC2 F l 2).length = 22 := by rw [List.length_append, hrl, selC2_length]
  have hrl' : (r.map (C2.val M)).length = 20 := by rw [List.length_map, hrl]
  rw [splitD_halfB]
  refine .cons ⟨⟨rfl, hK, hlen, by decide, ?_⟩, r.map (C2.val M), l, hl, hrl', hz, rfl⟩
    (.cons ⟨⟨rfl, hK, hlen, by decide, ?_⟩, r.map (C2.val M), l, hl, hrl', hz, rfl⟩ .nil)
  · show halfB 23 false _ _ = halfB 23 false _ _
    rw [hz, kre_val hw]
  · show halfB 23 true _ _ = halfB 23 true _ _
    rw [hz, kim_val hw]

/-- **The tape's `D` word claims** (four lanes; the point cells `r`, the value cells `v`) stand for V's. -/
theorem dhalves_rel {zc : Cell} {b : Bool} {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1)
    (hz2K : KC2 F.z2) (ho2K : KC2 F.o2) {r : List C2} (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) {v : List C2}
    (hv : ∀ l < 4, KC2 (v.getD l default)) {rv : List FE2} (hrv : rv = r.map (C2.val M)) {vv : List FE2}
    (hvv : ∀ l < 4, vv.getD l 0 = (v.getD l default).val M) :
    List.Forall₂ (FRelZ M zc b)
      ((List.range 4).flatMap fun l => [.dhalf false (r ++ selC2 F l 2) (v.getD l default).re,
        .dhalf true (r ++ selC2 F l 2) (v.getD l default).im])
      ((List.range 4).flatMap fun l => ((splitD 23 [(1, ⟨22, 0⟩, rv ++ E2V.selPtF l 2)] (vv.getD l 0)).zip
        (tailDE2 rv l)).map fun e => (Com.main, e.1, e.2)) := by
  refine forall₂_flatMap _ fun l hl => ?_
  have hl' := List.mem_range.mp hl
  rw [hrv, hvv l hl']
  exact dhalf_rel hz2 ho2 hz2K ho2K hr hrl hl' (hv l hl')


/-! ## Generic list facts -/

theorem forall₂_map_of {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ (L : List α), (∀ a ∈ L, R (f a) (g a)) → List.Forall₂ R (L.map f) (L.map g)
  | [], _ => .nil
  | a :: L, h => .cons (h a (List.mem_cons_self ..)) (forall₂_map_of L fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem zipIdx_map_range {α : Type} (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).zipIdx = (List.range n).map fun i => (f i, i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem mem_map_range {α : Type} {P : α → Prop} {f : ℕ → α} {n : ℕ} (h : ∀ l < n, P (f l)) :
    ∀ e ∈ (List.range n).map f, P e := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  exact h l (List.mem_range.mp hl)

theorem getD_mapV {l : List C2} {i : ℕ} (hi : i < l.length) :
    (l.map (C2.val M)).getD i 0 = (l.getD i default).val M := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem ld2_K (L : List ℕ) : ∀ x ∈ L.map Lvm.Q2.ld2, KC2 x := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨rfl, rfl⟩

/-! ## One claim -/

/-- A part of an `E2` sum claim on `K` cells, its point as long as its (regular) block's variables. -/
abbrev PartOk (e : C2 × Placement × List C2) : Prop :=
  KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧ e.2.1.variableCount ≤ CMain.nu20 ∧ RegP e.2.1

/-- **Half `h` of an `E2` sum claim** stands for V's half (regular blocks, zero tail). -/
theorem half_rel {zc : Cell} {b : Bool} (h : Bool) {parts : List (C2 × Placement × List C2)}
    {pv : List (FE2 × Placement × List FE2)} {w : Cell} {wv : FE}
    (hp : ∀ e ∈ parts, PartOk e) (hpv : partsV M parts = pv) (hw : w.val M = wv) :
    FRelZ M zc b (.half h parts w) (.main, halfB CMain.nu20 h pv wv, 0) :=
  ⟨⟨rfl, fun e he => ⟨(hp e he).1, (hp e he).2.1, (hp e he).2.2.1, (hp e he).2.2.2.1⟩, by rw [hpv, hw]⟩,
    fun e he => (hp e he).2.2.2.2, rfl⟩

theorem splitZ_eq (ν : ℕ) (pv : List (FE2 × Placement × List FE2)) (v : FE2) :
    splitZ ν pv v = [(.main, halfB ν false pv (FE.ofK v.re), 0), (.main, halfB ν true pv (FE.ofK v.im), 0)] := rfl

/-- **An `E2` sum claim's halves** stand for V's split claim. -/
theorem halves_rel {zc : Cell} {b : Bool} {parts : List (C2 × Placement × List C2)}
    {pv : List (FE2 × Placement × List FE2)} {v : C2} {vv : FE2}
    (hp : ∀ e ∈ parts, PartOk e) (hpv : partsV M parts = pv) (hv : KC2 v) (hvv : v.val M = vv) :
    List.Forall₂ (FRelZ M zc b) (halves parts v) (splitZ CMain.nu20 pv vv) := by
  rw [splitZ_eq]
  exact .cons (half_rel false hp hpv (by rw [kre_val hv, hvv])) (.cons (half_rel true hp hpv (by rw [kim_val hv, hvv]))
    .nil)

/-! ## `KS`'s `Y` parts -/

theorem ksYPart2_fst (p : Params) (F : FCtx) (l : ℕ) (pt : List C2) :
    (ksYPart2 p F l pt).1 = (ksYPartD p (layout0 p) l []).1 := by
  unfold ksYPart2 ksYPartD; by_cases hl : l < 14 <;> simp [hl]

theorem ksYPartD_fst (p : Params) (l : ℕ) (pt : List FE2) :
    (ksYPartD p (layout0 p) l pt).1 = (ksYPartD p (layout0 p) l []).1 := by
  unfold ksYPartD; by_cases hl : l < 14 <;> simp [hl]

theorem ksYPart2_snd {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (p : Params) (l : ℕ) (pt : List C2) :
    (ksYPart2 p F l pt).2.map (C2.val M) = (ksYPartD p (layout0 p) l (pt.map (C2.val M))).2 := by
  unfold ksYPart2 ksYPartD; by_cases hl : l < 14 <;> simp [hl, selC2_vals hz2 ho2]

theorem ksYPart2_K {F : FCtx} (hz2 : KC2 F.z2) (ho2 : KC2 F.o2) (p : Params) (l : ℕ) {pt : List C2}
    (hpt : ∀ x ∈ pt, KC2 x) : ∀ x ∈ (ksYPart2 p F l pt).2, KC2 x := by
  unfold ksYPart2; by_cases hl : l < 14
  · simp only [hl, ite_true]
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hpt x h
    · exact selC2_K hz2 ho2 _ _ x h
  · simp only [hl, ite_false]; exact hpt

theorem ksYPart2_len (p : Params) (F : FCtx) (l : ℕ) (pt : List C2) (hpt : pt.length = p.ksLog) :
    (ksYPart2 p F l pt).2.length = (ksYPart2 p F l pt).1.variableCount := by
  unfold ksYPart2; by_cases hl : l < 14 <;> simp [hl, hpt, selC2_length]

/-! ## The static blocks at `P20F` -/

/-- The front's `E2` claims' blocks at `p` are regular (`KS`, its `Y` lanes, the stream block's columns). -/
def RegsP (p : Params) : Prop := RegP ⟨p.ksLog + slotLog, (layout0 p).ks⟩ ∧
    (∀ l < 25, RegP (ksYPartD p (layout0 p) l []).1 ∧
      (ksYPartD p (layout0 p) l []).1.variableCount ≤ CMain.nu20) ∧
    (∀ l < 17, RegP ⟨p.ksLog, (layout0 p).s + l * 2 ^ p.recRowsLog⟩ ∧
      RegP ⟨ksXLog p, (layout0 p).s + l * 2 ^ p.recRowsLog + ksSplit p⟩ ∧
      RegP ⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩)

/-- The front's selector and sizes at `p` (`P20`'s). -/
def DselP (p : Params) : Prop := dSel p = 0 ∧ dSelBits p = 1 ∧ dBlock p = ⟨22, 0⟩ ∧ p.nuMain = CMain.nu20 ∧
    p.ksLog = 13 ∧ ksXLog p = 9 ∧ p.logN = 20 ∧ dLanes = 4

-- `regs_P20F`, `dsel_P20F` are in `LvmE2QHarFront` (S2GF/S2GT only; lvm2 U-TAPE).

/-! ## The boundary claims -/

theorem tailD_small {m : ℕ} (hm : m < 2 ^ 18) (z : List FE) : tailD (selectorPoint m 20 ++ z) = 0 := by
  have h18 : (selectorPoint m 20 ++ z).getD 18 0 = 0 := by
    rw [List.getD_append _ _ _ _ (by simp [selectorPoint_length'])]
    simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num : 18 < 20),
      Option.map_some, Option.getD_some, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hm, Nat.zero_mod]
    rfl
  have h19 : (selectorPoint m 20 ++ z).getD 19 0 = 0 := by
    rw [List.getD_append _ _ _ _ (by simp [selectorPoint_length'])]
    simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num : 19 < 20),
      Option.map_some, Option.getD_some, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (lt_trans hm (by norm_num) : m < 2 ^ 19), Nat.zero_mod]
    rfl
  rw [tailD, kappaD, h18, h19, add_zero, one_mul, CharTwo.add_self_eq_zero, zero_mul]

/-- **A boundary claim** `D̃_l(bits(n − 1) ‖ l) = h_l` stands for V's (tail `0`; small children: `n ≤ 2^18`). -/
theorem bound_rel {zc : Cell} {b : Bool} {mbE : List Cell} {N : ℕ} (hmb : vs M mbE = selectorPoint (N - 1) 20)
    (hsm : b = true → N ≤ 2 ^ 18) (hN : 1 ≤ N) {zE oE : ℕ} (hz : M.e zE = 0) (ho : M.e oE = 1) {l : ℕ} (w : ℕ) :
    FRelZ M zc b (.e3 ⟨.main, .point ⟨22, 0⟩ (mbE ++ Lvm.Har.selC zE oE l 2), kc w⟩)
      (.main, BlockClaim.point ⟨22, 0⟩ (selectorPoint (N - 1) 20 ++ selectorPoint l 2) (FE.ofK (M.k w)), 0) := by
  have hml : mbE.length = 20 := by
    have := congrArg List.length hmb; simpa [vs, selectorPoint_length'] using this
  have hlen : (mbE ++ Lvm.Har.selC zE oE l 2).length = 22 := by simp [hml, Lvm.Har.selC]
  have hv : vs M (mbE ++ Lvm.Har.selC zE oE l 2) = selectorPoint (N - 1) 20 ++ selectorPoint l 2 := by
    rw [vs, List.map_append, ← vs, ← vs, hmb, Lvm.Har.selC_vs hz ho]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_, fun hb => ?_⟩
  · show (decide (22 ≤ CMain.nu20) && decide ((mbE ++ Lvm.Har.selC zE oE l 2).length = 22)) = true
    rw [hlen]; rfl
  · show _ = BlockClaim.point ⟨22, 0⟩ (vs M (mbE ++ Lvm.Har.selC zE oE l 2)) ((kc w).val M)
    rw [hv, Cell.val_K]
  · show (if (⟨22, 0⟩ : Placement) = ⟨22, 0⟩ then decide ((mbE ++ Lvm.Har.selC zE oE l 2).length = 22)
      else decide (RegP (⟨22, 0⟩ : Placement))) = true
    simp [hlen]
  · show 0 = if (⟨22, 0⟩ : Placement) = ⟨22, 0⟩ then tailD (vs M (mbE ++ Lvm.Har.selC zE oE l 2)) else 0
    simp only [↓reduceIte, hv]
    rw [tailD_small (by have := hsm hb; (clear * - N mbE hN zE oE l this; omega))]

/-! ## The front's claims -/

/-- **`frontF`'s claims** from its gadgets' outputs (`frontF`'s list with the outputs as variables). -/
def frontCsF (p : Params) (F : FCtx) (r v ki kv : List C2) (wo : WireOut2) (rw : RowOut) (nuW : RowNu)
    (ko : Lvm.Q1.GkrOutE2) (rk : RowOut) (nuK : RowNu) (kl : KsLinkOut2) (mbE : List Cell) (omS : List C2) :
    List FClaim :=
  let L := layout0 p
  let blkD := dBlock p
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let rho' := kl.shift
  let xlo := rho'.take xl
  let om := kl.om
  let tape : List FClaim :=
    ((List.range dLanes).flatMap fun l =>
      let zl := r ++ selC2 F l 2
      let vl := v.getD l default
      [.dhalf false zl vl.re, .dhalf true zl vl.im]) ++
    [.drow (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)) nuW rw.target] ++
    (List.range 4).map fun l => .e3 ⟨.main, .point blkD (mbE ++ Lvm.Har.selC F.z.n F.o.n l 2), kc (hLane l)⟩
  let ks : List FClaim :=
    halves [(F.o2, ksBlk, ko.wordPoint)] ko.word ++ [.row ksBlk ko.slicePoint nuK rk.target]
  let ksOut : List FClaim := (List.range 25).flatMap fun l =>
    let bz := ksYPart2 p F l ki
    halves [(F.o2, bz.1, bz.2)] (kv.getD l default)
  let yParts := (List.range 25).map fun l => let bz := ksYPart2 p F l rho'; (om.getD l default, bz.1, bz.2)
  let inParts := (List.range 25).map fun l => (om.getD l default, ksBlk, rho' ++ selC2 F l slotLog)
  let mParts := (List.range 17).map (fun l => (om.getD l default, (⟨p.ksLog, L.s + l * R⟩ : Placement), rho')) ++
    (List.range 17).map (fun l => (omS.getD l default, (⟨xl, L.s + l * R + ksSplit p⟩ : Placement), xlo))
  let xParts := (List.range 17).map fun l => (om.getD l default, (⟨xl, L.x + l * R⟩ : Placement), xlo)
  let vY := kl.vals.getD 0 default
  let vIn := kl.vals.getD 1 default
  let vM := kl.vals.getD 2 default
  let vX := kl.vals.getD 3 default
  let link : List FClaim :=
    halves yParts vY ++ halves inParts vIn ++ [.half false xParts vX.re] ++ halves mParts vM ++
      [.half true xParts vX.im]
  tape ++ ks ++ ksOut ++ link


theorem rowValD_snd (z sv : List FE2) (e : List FE) : (rowValD z sv e).2 = e := rfl

theorem getD_K {l : List C2} (h : ∀ x ∈ l, KC2 x) {i : ℕ} (hi : i < l.length) : KC2 (l.getD i default) := by
  rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)

theorem partsV_range {n : ℕ} {f : ℕ → C2 × Placement × List C2} {g : ℕ → FE2 × Placement × List FE2}
    (h : ∀ l < n, (f l).1.val M = (g l).1 ∧ (f l).2.1 = (g l).2.1 ∧ (f l).2.2.map (C2.val M) = (g l).2.2) :
    partsV M ((List.range n).map f) = (List.range n).map g := by
  simp only [partsV, List.map_map]
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨e1, e2, e3⟩ := h l (List.mem_range.mp hl)
  simp only [Function.comp_apply, e1, e2, e3]

theorem partsV_append (a b : List (C2 × Placement × List C2)) : partsV M (a ++ b) = partsV M a ++ partsV M b :=
  List.map_append ..

set_option maxHeartbeats 1000000 in
/-- **The front's claims stand for V's** (`frontClaimsD p` at the phases' values; `p` with `P20`'s front facts: S2GF, S2GT), from the front gadgets'
outputs as variables: the tape's `D` word halves, row claim and boundary claims, `KS`'s word halves and row claim, its
25 output lanes, the link's `Y`, `in`, `X`, `M` halves. -/
theorem front_claimsG {p : Params} (hR : RegsP p) (hD : DselP p) {zc : Cell} {b : Bool} {pub : Pub} {F : FCtx} {r v ki kv : List C2} {wo : WireOut2}
    {rw : RowOut} {nuW : RowNu} {ko : Lvm.Q1.GkrOutE2} {rk : RowOut} {nuK : RowNu} {kl : KsLinkOut2}
    {mbE : List Cell} {omS : List C2} {tr tv tgl tsv cr cv csl : List FE2} {tk : E2V.KClaim FE2}
    {tfin tfo lfin : FE2} {eqW eqK : List FE}
    (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (hz2K : KC2 F.z2) (ho2K : KC2 F.o2) (hzE : M.e F.z.n = 0)
    (hoE : M.e F.o.n = 1)
    (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) (hv : ∀ l < 4, KC2 (v.getD l default))
    (htr : tr = r.map (C2.val M)) (htv : ∀ l < 4, tv.getD l 0 = (v.getD l default).val M)
    (hsgK : ∀ x ∈ wo.sigma, KC2 x) (hsgl : wo.sigma.length = 20) (htaK : ∀ x ∈ wo.tau, KC2 x)
    (htal : wo.tau.length = 2)
    (htr1 : (rowValD (wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ E2V.selPtF (dSel p) (dSelBits p))
      tsv eqW).1.1 = rw.target.val M)
    (hnuW : RowNuOk M nuW eqW)
    (hmbE : vs M mbE = selectorPoint (pub.n - 1) 20) (hh : pub.h = (List.range 4).map fun l => M.k (hLane l))
    (hsm : b = true → pub.n ≤ 2 ^ 18) (hn : 1 ≤ pub.n)
    (hwpK : ∀ x ∈ ko.wordPoint, KC2 x) (hwpl : ko.wordPoint.length = 19) (hwK : KC2 ko.word)
    (hspK : ∀ x ∈ ko.slicePoint, KC2 x) (hspl : ko.slicePoint.length = 19)
    (hcr1 : (rowValD (ko.slicePoint.map (C2.val M)) csl eqK).1.1 = rk.target.val M) (hnuK : RowNuOk M nuK eqK)
    (hkiK : ∀ x ∈ ki, KC2 x) (hkil : ki.length = 13) (hcr : cr = ki.map (C2.val M))
    (hkvK : ∀ l < 25, KC2 (kv.getD l default)) (hcv : ∀ l < 25, cv.getD l 0 = (kv.getD l default).val M)
    (hshK : ∀ x ∈ kl.shift, KC2 x) (hshl : kl.shift.length = 13) (hkcl : kl.kchal.length = 18)
    (homK : ∀ x ∈ kl.om, KC2 x)
    (hom : kl.om.map (C2.val M) = E2V.eqKernelF ((kl.kchal.drop p.ksLog).map (C2.val M)))
    (hsel : kl.sel.val M = E2V.selXF (ksXLog p) (kl.shift.map (C2.val M)))
    (homS : ∀ l < 17, KC2 (omS.getD l default) ∧
      (omS.getD l default).val M = (kl.om.getD l default).val M * kl.sel.val M)
    (hvl : kl.vals.length = 4) (hvK : ∀ x ∈ kl.vals, KC2 x) :
    List.Forall₂ (FRelZ M zc b) (frontCsF p F r v ki kv wo rw nuW ko rk nuK kl mbE omS)
      (frontClaimsD p pub
        (tr, tv, tk, ((wo.sigma.map (C2.val M), tfin), tgl, ((wo.tau.map (C2.val M), tfo), tsv,
          rowValD (wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ E2V.selPtF (dSel p) (dSelBits p))
            tsv eqW)))
        (cr, cv, ([(ko.wordPoint.map (C2.val M), ko.word.val M)], ko.slicePoint.map (C2.val M), csl),
          rowValD (ko.slicePoint.map (C2.val M)) csl eqK)
        (kl.kchal.map (C2.val M), (kl.shift.map (C2.val M), lfin), kl.vals.map (C2.val M))) := by
  obtain ⟨hdS, hdB, hdBl, hnu, hksL, hxl, hlogN, hdL⟩ := hD
  obtain ⟨rK, rY, rS⟩ := hR
  have h19 : (19 : ℕ) = p.ksLog + slotLog := by rw [hksL]; rfl
  have homl : kl.om.length = 32 := by
    have := congrArg List.length hom
    rw [List.length_map, E2V.eqKernelF_length] at this
    rw [this]; simp [hkcl, hksL]
  have homg : ∀ l < 32, (kl.om.getD l default).val M =
      (E2V.eqKernelF ((kl.kchal.map (C2.val M)).drop p.ksLog)).getD l 0 := fun l hl => by
    rw [← getD_mapV (by (clear * - l kl p pub r ki wo ko homl hl; omega)), hom, List.map_drop]
  have hvv : ∀ k < 4, (kl.vals.getD k default).val M = (kl.vals.map (C2.val M)).getD k 0 := fun k hk =>
    (getD_mapV (by (clear * - k kl p pub r ki wo ko hvl hk; omega))).symm
  have hvK' : ∀ k < 4, KC2 (kl.vals.getD k default) := fun k hk => getD_K hvK (by (clear * - k kl p pub r ki wo ko hvl hk; omega))
  have homK' : ∀ l < 25, KC2 (kl.om.getD l default) := fun l hl => getD_K homK (by (clear * - l kl p pub r ki wo ko homl hl; omega))
  have hselC : ∀ l, ∀ x ∈ kl.shift ++ selC2 F l slotLog, KC2 x := fun l x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hshK x h
    · exact selC2_K hz2K ho2K _ _ x h
  have htakeK : ∀ x ∈ kl.shift.take (ksXLog p), KC2 x := fun x hx => hshK x (List.mem_of_mem_take hx)
  have htakel : (kl.shift.take (ksXLog p)).length = ksXLog p := by simp [hshl, hxl]
  simp only [frontCsF, frontClaimsD]
  rw [hnu]
  refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_
  · -- the tape
    refine List.rel_append (List.rel_append ?_ ?_) ?_
    · rw [hdBl, hdL]
      exact dhalves_rel hz2 ho2 hz2K ho2K hr hrl hv htr htv
    · have hzz : (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)).map (C2.val M) =
          wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ E2V.selPtF (dSel p) (dSelBits p) := by
        simp only [List.map_append, selC2_vals hz2 ho2]
      have hzl : (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)).length = CMain.nu20 := by
        simp only [List.length_append, hsgl, htal, selC2_length, hdB]
      have hzK : ∀ x ∈ wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p), KC2 x := fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hsgK x h
          · exact htaK x h
        · exact selC2_K hz2K ho2K _ _ x h
      refine .cons ⟨⟨rfl, eqW, hnuW, ?_, hzK, hzl, le_refl _, ?_⟩, ?_, eqW, hnuW, by rw [hzz, rowValD_snd]⟩ .nil
      · intro e; rw [e] at hzl; simp at hzl
      · show (⟨⟨CMain.nu20, 0⟩, (rowValD _ _ eqW).1.2, (rowValD _ _ eqW).1.1⟩ : BlockClaim) = _
        rw [htr1, rowValD_weight, hzz]
      · rw [hzz, List.getD_append_right _ _ _ _ (by simp [hsgl, htal]), hdS, hdB]
        simp [hsgl, htal, E2V.selPtF]
    · rw [hh, zipIdx_map_range, List.map_map, hdBl, hlogN]
      exact forall₂_map_of _ fun l _ => bound_rel hmbE hsm hn hzE hoE (hLane l)
  · -- `KS`: the word halves, the row claim
    refine List.rel_append ?_ (.cons ⟨⟨rfl, eqK, hnuK, ?_, hspK, hspl.trans h19,
      by show p.ksLog + slotLog ≤ CMain.nu20; rw [hksL]; decide, ?_⟩, rK, rfl⟩ .nil)
    · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine halves_rel ?_ (by simp only [partsV, List.map_cons, List.map_nil, ho2]) hwK rfl
      simp only [List.mem_singleton, forall_eq]
      exact ⟨ho2K, hwpK, hwpl.trans h19, by show p.ksLog + slotLog ≤ CMain.nu20; rw [hksL]; decide, rK⟩
    · intro e; rw [e] at hspl; simp at hspl
    · show (⟨_, (rowValD _ _ eqK).1.2, (rowValD _ _ eqK).1.1⟩ : BlockClaim) = _
      rw [hcr1, rowValD_weight]
  · -- `KS`'s 25 output lanes
    refine forall₂_flatMap _ fun l hl => ?_
    have hl' := List.mem_range.mp hl
    refine halves_rel ?_ ?_ (hkvK l hl') (hcv l hl').symm
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨ho2K, ksYPart2_K hz2K ho2K _ _ hkiK, ksYPart2_len _ _ _ _ (hkil.trans hksL.symm), ?_, ?_⟩ <;>
        rw [ksYPart2_fst]
      · exact (rY l hl').2
      · exact (rY l hl').1
    · simp only [partsV, List.map_cons, List.map_nil, ho2, ksYPart2_snd hz2 ho2, hcr, ksYPart2_fst, ksYPartD_fst]
  · -- the link
    have hY : ∀ l < 25, KC2 (kl.om.getD l default) ∧ (∀ x ∈ (ksYPart2 p F l kl.shift).2, KC2 x) ∧
        (ksYPart2 p F l kl.shift).2.length = (ksYPart2 p F l kl.shift).1.variableCount ∧
        (ksYPart2 p F l kl.shift).1.variableCount ≤ CMain.nu20 ∧ RegP (ksYPart2 p F l kl.shift).1 :=
      fun l hl => ⟨homK' l hl, ksYPart2_K hz2K ho2K _ _ hshK, ksYPart2_len _ _ _ _ (hshl.trans hksL.symm),
        by rw [ksYPart2_fst]; exact (rY l hl).2, by rw [ksYPart2_fst]; exact (rY l hl).1⟩
    have hxv : ∀ l < 17, (kl.om.getD l default).val M =
        (E2V.eqKernelF ((kl.kchal.map (C2.val M)).drop p.ksLog)).getD l 0 := fun l hl => homg l (by (clear * - l p pub r ki wo ko kl hl; omega))
    have hX : partsV M ((List.range 17).map fun l => (kl.om.getD l default,
          (⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩ : Placement), kl.shift.take (ksXLog p))) =
        (List.range 17).map fun l => ((E2V.eqKernelF ((kl.kchal.map (C2.val M)).drop p.ksLog)).getD l 0,
          (⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩ : Placement),
          (kl.shift.map (C2.val M)).take (ksXLog p)) :=
      partsV_range fun l hl => ⟨hxv l hl, rfl, List.map_take ..⟩
    have hXp : ∀ e ∈ (List.range 17).map (fun l => (kl.om.getD l default,
          (⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩ : Placement), kl.shift.take (ksXLog p))),
        KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧ e.2.1.variableCount ≤ CMain.nu20 ∧
          RegP e.2.1 :=
      mem_map_range fun l hl => ⟨homK' l (by (clear * - l p pub r ki wo ko kl hl; omega)), htakeK, htakel, by show ksXLog p ≤ CMain.nu20; rw [hxl]; decide,
        (rS l hl).2.2⟩
    refine List.rel_append (List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_) ?_
    · refine halves_rel (mem_map_range hY) (partsV_range fun l hl => ⟨homg l (by (clear * - l p pub r ki wo ko kl hl; omega)), ?_, ?_⟩)
        (hvK' 0 (by (clear * - p pub r ki wo ko kl; omega))) (hvv 0 (by (clear * - p pub r ki wo ko kl; omega)))
      · simp only [ksYPart2_fst, ksYPartD_fst]
      · simp only [ksYPart2_snd hz2 ho2]
    · refine halves_rel (mem_map_range fun l hl => ⟨homK' l hl, hselC l, ?_,
        by show p.ksLog + slotLog ≤ CMain.nu20; rw [hksL]; decide, rK⟩)
        (partsV_range fun l hl => ⟨homg l (by (clear * - l p pub r ki wo ko kl hl; omega)), rfl, ?_⟩) (hvK' 1 (by (clear * - p pub r ki wo ko kl; omega))) (hvv 1 (by (clear * - p pub r ki wo ko kl; omega)))
      · simp [hshl, selC2_length, hksL]
      · rw [List.map_append, selC2_vals hz2 ho2]
    · rw [splitZ_eq, List.take_succ_cons, List.take_zero]
      exact .cons (half_rel false hXp hX (by rw [kre_val (hvK' 3 (by (clear * - p pub r ki wo ko kl; omega))), hvv 3 (by (clear * - p pub r ki wo ko kl; omega))])) .nil
    · refine halves_rel ?_ ?_ (hvK' 2 (by (clear * - p pub r ki wo ko kl; omega))) (hvv 2 (by (clear * - p pub r ki wo ko kl; omega)))
      · intro e he
        rcases List.mem_append.mp he with h | h
        · refine mem_map_range (P := PartOk) ?_ e h
          intro l hl
          exact ⟨homK' l (by (clear * - l p pub r ki wo ko kl hl; omega)), hshK, by rw [hshl, hksL],
            by show p.ksLog ≤ CMain.nu20; rw [hksL]; decide,
            (rS l hl).1⟩
        · refine mem_map_range (P := PartOk) ?_ e h
          intro l hl
          exact ⟨(homS l hl).1, htakeK, htakel, by show ksXLog p ≤ CMain.nu20; rw [hxl]; decide, (rS l hl).2.1⟩
      · rw [partsV_append]
        congr 1
        · exact partsV_range fun l hl => ⟨homg l (by (clear * - l p pub r ki wo ko kl hl; omega)), rfl, rfl⟩
        · exact partsV_range fun l hl => ⟨by rw [(homS l hl).2, homg l (by (clear * - l p pub r ki wo ko kl hl; omega)), hsel], rfl, List.map_take ..⟩
    · rw [splitZ_eq, List.drop_succ_cons, List.drop_zero]
      exact .cons (half_rel true hXp hX (by rw [kim_val (hvK' 3 (by (clear * - p pub r ki wo ko kl; omega))), hvv 3 (by (clear * - p pub r ki wo ko kl; omega))])) .nil

end Lvm.E2Q
