-- New for lvm2 σ_LEAF (SLF-L, 2026-11-16): the merged tape over a LIST of `cont` intervals (the third interval of
-- S2GS: the node's own key-leaf hash), S2GS's good pair and middle phases. DAY-0 STATEMENTS: every `sorry` is tagged
-- `-- SLF-STMT <n>`. A proof never changes its statement; a needed change goes to the lead old → new.
import LvmS2GLMid
import LvmS2GSHdr
import LvmS2GSFront

/-!
# The merged tape over a list of `cont` intervals; S2GS's middle phases

* **`GkL iv`**: the Keccak half over the list-generic tape (`LvmS2GSFront`); `GkL (contIvB b) = GkB b` (`rfl`).
* **KS bridge** (SLF-STMT 2a–2c): `spongeRel_of_GkL`, `traceDigest_of_GkL`, `sigKSin_of_GkL` (the `b`-generic
  `spongeRel_of_GkB`, `traceDigest_of_GkB`, `sigKSin_of_GkB` over a list with the row facts as hypotheses).
* **S2GS** (`Lvm.E2S`): `bS = 3,951` (`bS_eq`), the own key leaf's first `KS` row `aSP` (`7,632`, layout D6), `contIvS a = [(1, bS), (8080, 8110), (a + 1, a + 31)]`; `GbTS`, `THypS`, `GoodTS`
  (`pubXTS`: no `σ_leaf` lanes, `acc_in` at byte 152), `midGS`, `midSpecP_GS` (SLF-STMT 6m).
-/

set_option autoImplicit false

namespace Lvm.E2U

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)

/-- **The Keccak half of a good pair over `iv`** (`GkB`'s twin). -/
def GkL (iv : List (ℕ × ℕ)) (x : List UInt8) (p : LeanVM.Protocol.Column CMain.nu20 × LeanVM.Protocol.Column 19) :
    Prop :=
  TapeRelL iv (Lvm.ASM.hdrOf x).s (Lvm.ASM.hdrOf x).n (Lvm.NS.colM p.1)

theorem GkL_contIvB (b : ℕ) : GkL (contIvB b) = GkB b := rfl

end Lvm.E2U

namespace Lvm.E2U

open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **SLF-STMT 2a** (owner L): **the sponge half over `iv` is a sponge table** when row `0` starts a sponge
(`spongeRel_of_GkB` over a list). -/
theorem spongeRel_of_GkL {iv : List (ℕ × ℕ)} {x : List UInt8} {p : Column CMain.nu20 × Column 19}
    (h0 : contL iv 0 = false) (hG : GkL iv x p) :
    SpongeRel 13 (ksVirt 13 (YqU p.1) (MqU p.1) (contL iv)) (YqU p.1) (MqU p.1) (contL iv) where
  out i hi l hl := by
    rw [YqU, hG.2 i hi l hl, tapeInL, tapeIn, if_neg (by (clear * -; omega)), if_pos (by (clear * - hi; omega)),
      Nat.add_sub_cancel_left]
  link i hi l hl := by
    rw [ksVirt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 13), Nat.div_eq_of_lt hi, zero_add]
  cont0 := h0

/-- **SLF-STMT 2b** (owner L): **the sponge half over `iv` outputs the child's trace digest** at row `B − 1` when the
trace's rows `1 … B − 1` continue (`traceDigest_of_GkB` over a list). -/
theorem traceDigest_of_GkL {P : Params} {iv : List (ℕ × ℕ)} {x : List UInt8} {qm : Column CMain.nu20}
    {qr : Column 19}
    (hst : StreamOk P) (h0 : contL iv 0 = false)
    (hin : ∀ i, 0 < i → i < spongeBlocks P → contL iv i = true)
    (hsb : spongeBlocks P = Lvm.KSponge.nBlk (hashedLen P)) (hB : spongeBlocks P ≤ 7680)
    (hG : GkL iv x (qm, qr)) (hS : SBlkU qm qr) (hL : LaneLink P (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P)) :
    Lvm.KSponge.stDigest (yState (YqU qm) (spongeBlocks P - 1)) =
      traceDigest (decode P (wsOf (Lvm.X.laneOf (wOfCol qr)))) := by
  have H := spongeRel_of_GkL h0 hG
  have hS' := stream_of_laneLink hst hL
  have hsz : hashedLen P ≤ (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).length := by
    rw [wordsBytes_length]; exact hL.size
  have hin' : ∀ i, 0 < i → i < Lvm.KSponge.nBlk (hashedLen P) → contL iv i = true :=
    fun i h1 h2 => hin i h1 (by rw [hsb]; exact h2)
  rw [hsb] at hB ⊢
  obtain ⟨L, hL⟩ : ∃ L, hashedLen P = L := ⟨_, rfl⟩
  rw [hL] at hS' hsz hpad hB hin' ⊢
  have hnbL : Lvm.KSponge.nBlk L = L / 136 + 1 := rfl
  refine traceDigest_of_KS 13 _ (YqU qm) (MqU qm) _ H L (le_trans hB (by norm_num)) hin' ?_ _ ?_
  · intro p h1 h2
    have h2' : p < 136 * Lvm.KSponge.nBlk L := h2
    have := msgBytes_eq_streamU hS (p := p) (by show p / 136 < 2 ^ 14; omega)
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, this, ← padAt_eq]
    exact hpad p h1 (by rw [nBlk_eq]; omega)
  · rw [← hS']
    refine List.ext_getElem (by rw [Lvm.KSponge.streamOf_length, List.length_take]; omega) fun p h1 h2 => ?_
    have hp : p < L := by rw [Lvm.KSponge.streamOf_length] at h1; exact h1
    simp only [Lvm.KSponge.streamOf, List.getElem_ofFn, List.getElem_take]
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl,
      msgBytes_eq_streamU hS (by show p / 136 < 2 ^ 14; omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **SLF-STMT 2c** (owner L): **Q_sig's `KS` inputs over `iv`** when Q_sig's 449 rows from `ksSplit P20` continue
exactly on its key leaf's rows `400 … 430` (`sigKSin_of_GkB` over a list). -/
theorem sigKSin_of_GkL {iv : List (ℕ × ℕ)} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} {I : SigIn}
    {v : ℕ → FK} (h0 : contL iv 0 = false)
    (hcF : ∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) → contL iv (ksSplit P20 + r) = false)
    (hcT : ∀ r, 400 ≤ r → r ≤ 430 → contL iv (ksSplit P20 + r) = true)
    (hG : GkL iv x (qm, qr))
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 430 + t) l))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 447) l))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 448) l)) :
    SigKSin I v := by
  have H := spongeRel_of_GkL h0 hG
  have hrow : ∀ r < 449, ksSplit P20 + r < 2 ^ 13 := fun r hr => by rw [ksSplit_P20]; omega
  -- a one-block row
  have one : ∀ r < 449, ¬ (400 ≤ r ∧ r ≤ 430) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l)) →
      OneHash v (fun l => I.xs + 17 * r + l) y := fun r hr hn y hy =>
    ⟨yState (YqU qm) (ksSplit P20 + r), by
      rw [xorMsg_cellsU (qm := qm) (r := r) (fun l hl => hx r hr l hl)]
      exact oneRow_perm 13 _ (YqU qm) (MqU qm) _ H (hrow r hr) (hcF r hr hn),
      digAt_of_cells hy⟩
  refine ⟨fun r hr => one r (by (clear * - hr; omega)) (by (clear * - hr; omega)) _ (hys r hr), ?_, fun t ht => ?_,
    one 447 (by (clear * -; omega)) (by (clear * -; omega)) _ hyls,
    one 448 (by (clear * -; omega)) (by (clear * -; omega)) _ hyns⟩
  · -- the key leaf: rows `S + 399 … S + 430`
    refine ⟨fun u => prevState (YqU qm) (contL iv) (ksSplit P20 + (399 + u)),
      fun u => yState (YqU qm) (ksSplit P20 + (399 + u)), ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · simp only [prevState, Nat.add_zero, hcF 399 (by (clear * -; omega)) (by (clear * -; omega))]; rfl
    · rw [xorMsg_cellsU (qm := qm) (r := 399 + u) (fun l hl => hx _ (by (clear * - hu; omega)) l hl)]
      exact row_perm 13 _ (YqU qm) (MqU qm) _ H (hrow _ (by (clear * - hu; omega)))
    · simp only [prevState, hcT (399 + (u + 1)) (by (clear * - hu; omega)) (by (clear * - hu; omega)), if_true]
      congr 1
    · refine digAt_of_cells fun l hl => ?_
      have := hyc 0 (by (clear * -; omega)) l hl
      simpa using this
  · -- path node `t`: row `S + 431 + t`
    refine one (431 + t) (by (clear * - ht; omega)) (by (clear * - ht; omega)) _ fun l hl => ?_
    have := hyc (t + 1) (by (clear * - ht; omega)) l hl
    rw [show ksSplit P20 + 430 + (t + 1) = ksSplit P20 + (431 + t) by (clear * -; omega)] at this
    exact this

end Lvm.E2U

namespace Lvm.E2S

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.E2U Lvm.E2L Lvm.Typed LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Compile
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26 mbLinB)
open Lvm.VEq (hdX pubX)
open Lvm.ASM (OpenClaims GoodRel εS Pair BndS)
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.Typed (BT)
open scoped ENNReal

/-- **The S2GS trace's sponge blocks less one**: the wire's first `cont` interval is `[1, bS]`. -/
abbrev bS : ℕ := 3951

/-- **SLF-STMT 2d** (owner L): `spongeBlocks P20S = bS + 1` (`sizes_P20S`). -/
theorem bS_eq : spongeBlocks P20S = bS + 1 := sizes_P20S.1.2.2.2.2.1

/-- **The own key leaf's first `KS` row** at S2GS (layout D6, frozen: the second walk at rows `[7233, 7680)`, its key
leaf `7632 … 7663`). -/
abbrev aSP : ℕ := 7632

/-- **S2GS's `cont` intervals** (SLF-STMT 2, `contIvS`): the trace's rows `1 … bS`, Q_sig's key leaf `8080 … 8110`,
the node's own key leaf `a + 1 … a + 31` (`a` its first row). -/
def contIvS (a : ℕ) : List (ℕ × ℕ) := [(1, bS), (8080, 8110), (a + 1, a + 31)]

/-- **SLF-STMT 2e** (owner L): `contIvS aSP`'s row facts: row `0` starts a sponge, the trace's rows `1 … bS` continue,
Q_sig's 449 rows continue exactly on `400 … 430`, the own key leaf's rows `aSP + 1 … aSP + 31` continue, and the
own key leaf lies between the trace and `ksSplit P20` (`decide`). -/
theorem contIvS_ok : contL (contIvS aSP) 0 = false ∧ (∀ i, 0 < i → i ≤ bS → contL (contIvS aSP) i = true) ∧
    (∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) → contL (contIvS aSP) (ksSplit P20 + r) = false) ∧
    (∀ r, 400 ≤ r → r ≤ 430 → contL (contIvS aSP) (ksSplit P20 + r) = true) ∧
    (∀ u, 0 < u → u < 32 → contL (contIvS aSP) (aSP + u) = true) ∧ contL (contIvS aSP) aSP = false ∧
    bS + 1 < aSP ∧ aSP + 32 ≤ ksSplit P20 := by
  have hk : ksSplit P20 = 7680 := ksSplit_P20
  rw [hk]
  refine ⟨by decide, fun i h1 h2 => ?_, fun r h1 h2 => ?_, fun r h1 h2 => ?_, fun u h1 h2 => ?_, by decide, by decide,
    by decide⟩
  all_goals
    unfold bS aSP at *
    simp only [contL, contIvS, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.or_eq_false_iff,
      decide_eq_true_eq, decide_eq_false_iff_not, bS]
    omega

/-- **The good pair's typed half at S2GS** (`GbTB` at `pubXTS`). -/
def GbTS (Ti : TInst) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ) (x : List UInt8) (p : Pair) : Prop :=
  (TGoodT Ti lay26 hτ (pubXTS x) p ∧ BndS x p.1) ∧ AccOkTT Ti (pubXTS x)

/-- **The S2GS instance's hypotheses** (`THypL` at `pubXTS`). -/
structure THypS (Ti : TInst) : Prop where
  ok : Ti.Ok
  maps : Ti.MapsFit lay26
  acc : ∀ x, (pubXTS x).accIn.pt.length = phiVarsT
  accC2 : ∀ x, (∀ a ∈ (pubXTS x).accIn.pt, a.c₂ = 0) ∧ (pubXTS x).accIn.y.c₂ = 0
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ
  sc : AllSc Ti.mbT
  layOk : LayOk lay26 Ti.mbT
  keys : KeysOk Ti.mbT
  width : ∀ t ∈ Ti.mbT, 0 < t.w
  fix : FixOk Ti.mbT
  widths : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38
  lin : mbLinB Ti.mbT = true
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = miniDepth
  errs : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), TErrsL 1 (inst lay26 Ti.mbT h) εS 0

/-- **The good pair at S2GS**: `GbTS` and the merged tape over `contIvS aSP`. -/
def GoodTS (Ti : TInst) (H : THypS Ti) : GoodRel := fun x qm qr ↦ GbTS Ti H.hτ x (qm, qr) ∧ GkL (contIvS aSP) x (qm, qr)

/-- **S2GS's middle phases**: S2GL's typed phases on `pubXTS`, the merged tape over `contIvS aSP`, the claims. -/
def midGS (Ti : TInst) (x : List UInt8) : VerifierProgram OpenClaims :=
  typedProgL Ti (pubXTS x) >>= fun a ↦ tapeProgL (contIvS aSP) (hdX x).s (pubX x).n >>= fun k ↦
    pure (assembleU₂ x a k)

/-- `contIvS aSP` is well placed. -/
theorem ivOk_contIvS : IvOk (contIvS aSP) := by
  refine ⟨fun ab hab ↦ ?_, ?_⟩
  · simp only [contIvS, List.mem_cons, List.mem_nil_iff, or_false] at hab
    rcases hab with rfl | rfl | rfl <;> (simp only [bS, aSP]; omega)
  · simp only [contIvS, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.not_mem_nil, false_imp_iff, implies_true, List.Pairwise.nil, and_true, bS, aSP]
    omega

/-- The S2GS wire commits nothing and asks no proof of work. -/
theorem cg_wireProgL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim LeanVM.Parameters.E2) :
    Lvm.M3.NoCG (wireProgL iv s n claim) :=
  Lvm.M3.NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_e2Reads _) fun _ ↦
    Lvm.M3.NoCG.bind (Lvm.M3.cg_require _) fun _ ↦ Lvm.M3.NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦
        Lvm.M3.cg_ret _

/-- The S2GS tape commits nothing and asks no proof of work. -/
theorem cg_tapeProgL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) : Lvm.M3.NoCG (tapeProgL iv s n) :=
  Lvm.M3.NoCG.bind cg_e2Sep fun _ ↦ Lvm.M3.NoCG.bind (cg_e2Samples _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_e2Reads _) fun _ ↦ Lvm.M3.NoCG.bind (cg_e2Samples _ _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_tapeGkrE2 _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (Lvm.M3.cg_require _) fun _ ↦
        Lvm.M3.NoCG.bind (cg_wireProgL _ _ _ _) fun _ ↦ Lvm.M3.cg_ret _

theorem retOK_wireProgL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    RetOK (fun wo : WireOutU ↦ IsMultiaffine 23 wo.d.row.2 ∧ IsMultiaffine 23 wo.y.row.2 ∧
      IsMultiaffine 23 wo.m.row.2) (wireProgL iv s n claim) :=
  (retOK_sumcheckE2 _ _ _ _).bind fun sc hsc ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_slotProgE2U 2 1 0 _ _ _ (by simp [hsc])).bind fun d hd ↦
    (retOK_slotProgE2U 5 5 22 _ _ _ (by simp [hsc])).bind fun y hy ↦
    (retOK_slotProgE2U 5 4 10 _ _ _ (by simp [hsc])).bind fun m hm ↦ RetOK.ret ⟨hd, hy, hm⟩

/-- **Every return of the S2GS tape meets `KgRetU`.** -/
theorem retOK_tapeProgL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) : RetOK KgRetU (tapeProgL iv s n) :=
  RetOK.bind_true fun _ ↦ (retOK_e2Samples _ _).bind fun r hr ↦ (retOK_e2Reads _).bind fun ab hab ↦
    (retOK_e2Samples _ _).bind fun r20 h20 ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_wireProgL _ _ _ _).bind fun wo hwo ↦ RetOK.ret ⟨by simp [hr, h20], hab, hwo⟩

/-- `THypS`'s facts as S2GL's `THypL` (the `acc_in` facts of `pubXT` hold for every statement). -/
theorem THypS.toL {Ti : TInst} (H : THypS Ti) : THypL Ti :=
  { ok := H.ok, maps := H.maps, acc := fun x ↦ Lvm.VEq.length_pubXT x, accC2 := fun x ↦ Lvm.VEq.c₂_pubXT x,
    hτ := H.hτ, sc := H.sc, layOk := H.layOk, keys := H.keys, width := H.width, fix := H.fix, widths := H.widths,
    lin := H.lin, μBus := H.μBus, errs := H.errs }

/-- **The typed phases at S2GS on the viewed pinned pairs** (`specBusGL` at `pubXTS`). -/
noncomputable def specBusGS {Ti : TInst} (H : THypS Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) (x : List UInt8) (Gk N : Lvm.ASM.Pair → Prop) :
    Spec (typedProgL Ti (pubXTS x))
      (fun h ↦ Lvm.E2F.PinPost za h ∧
        Doomed (Lvm.E2F.candRelZ recOf za x)
          (fun p ↦ GbTS Ti H.hτ x (Lvm.Shape.vp x p) ∧ (Gk (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p))) h)
      (fun a h ↦ Doomed (Lvm.E2F.candRelZ recOf za x)
        (fun p ↦ (BT x a (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p)) ∧
          (Gk (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p))) h ∧ Lvm.E2F.PinPost za h)
      εS leadF₂ 0 :=
  have S0 := typedSpecGL Ti (pubXTS x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.fix H.lin (H.μBus H.hτ)
    (imgCZ recOf za x) (fun p ↦ Lvm.ASM.BndS x p.1 ∧ Gk p ∧ N p) (L₀ := 1) (εmax := εS) (T := 0)
    (fun h ↦ 1 ≤ (commits h).length) (imgCZ_append recOf za x) (fun _ ↦ Set.toFinite _)
    (imgCZ_ncard_le_one recOf za x) (H.errs H.hτ)
  (S0.frame (Lvm.E2F.PinPost za) (fun _ _ hl hr ↦ pinPost_append za
      ((noCG_typedProgL Ti (pubXTS x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.Typed.rootShapeM_one hr.1, Lvm.Typed.rootShapeM_firstWord hr.1,
      doomed_imgCZ.mpr (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCZ.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩,
      hp.2⟩)
    le_rfl zero_le le_rfl

/-- **SLF-STMT 6m** (owner L): **S2GS's middle phases' specification** (`midSpecP_GL`'s twin at `midGS`, `GoodTS`). -/
theorem midSpecP_GS (Ti : TInst) (H : THypS Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) :
    Lvm.ASM.MidSpecPτ (midGS Ti) (Lvm.E2F.candRelZ recOf za) (Lvm.E2F.PinPost za)
      (Lvm.Shape.Good₂ (GoodTS Ti H)) εS leadF₂ τU := by
  have hS : E2V.SplitSound := fun nu c hc q h ↦ splitE2_sound nu c hc q h
  have hA : E2V.SplitAffine := fun nu c hc ↦ isMultiaffine_splitE2 nu c hc
  have h7 : (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) ≤ εS := by
    simpa using E2V.sum7_le_εS
  exact Lvm.ASM.midSpecOfRelGτ (busP := fun x ↦ typedProgL Ti (pubXTS x))
    (kgP := fun x ↦ tapeProgL (contIvS aSP) (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleU₂ x a k) (Lb := leadF₂) (Lk := 0)
    (Gb := fun x p ↦ GbTS Ti H.hτ x (Lvm.Shape.vp x p)) (Gk := fun x p ↦ GkL (contIvS aSP) x (Lvm.Shape.vp x p))
    (B := fun x a p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p))
    (Kc := fun x k p ↦ KcU (Lvm.NS.colM (Lvm.Shape.vp x p).1) k)
    (Qa := fun _ a ↦ (∀ c ∈ a.1, LeanVM.Protocol.Whir.Sound.IsMultiaffine 19 c.1) ∧
      (∀ c ∈ a.2, LeanVM.Protocol.Whir.Sound.IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39)
    (Qk := fun _ ↦ KgRetU) (C := Lvm.E2F.candRelZ recOf za) (Sh := Lvm.E2F.PinPost za)
    (fun _ _ hl hr ↦ E2V.pinPost_append za hl hr)
    (fun x ↦ specBusGS H recOf za x (GkL (contIvS aSP) x) fun p ↦ ¬ (GbTS Ti H.hτ x p ∧ GkL (contIvS aSP) x p))
    (fun x ↦ retOK_typedProgL Ti H.toL (pubXTS x))
    (fun x a T hT ↦ (tapeSpecLW ivOk_contIvS (E2V.candRelZ_stable recOf za x) (E2V.candRelZ_ncard_le recOf za x)
        (hdX x).s (n := (pubX x).n) (fun p ↦ Lvm.NS.colM (Lvm.Shape.vp x p).1)
        (fun p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p) ∧
          ¬ (GbTS Ti H.hτ x (Lvm.Shape.vp x p) ∧ GkL (contIvS aSP) x (Lvm.Shape.vp x p)))
        (calc (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) + T
            ≤ (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) +
                (εS - ∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) := add_le_add le_rfl hT
          _ = εS := add_tsub_cancel_of_le h7)).mono
      (fun _ hd ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hd fun p ⟨ht, hb, hn⟩ ↦
        ⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hn⟩, hb, hn⟩)
      (fun _ _ hp ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hp.2.2.2 fun p ⟨⟨h1, h2, h3, h4, h5⟩, hR⟩ ↦
        ⟨h1, h2, h3, h4, h5, hR⟩) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_tapeProgL _ _ _) (fun _ ↦ cg_tapeProgL _ _ _)
    (fun x a k p _ hk h1 h2 ↦ linkU hS x a k p hk h1 h2)
    (fun x a k ha hk ↦ sideU hA x a k ha hk)

end Lvm.E2S
